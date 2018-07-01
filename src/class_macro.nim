
import macros,sequtils,tables#,hashes,future,strutils
# import macros
using 
  node*:NimNode
  value*:NimNode
proc return_param*(node): NimNode {.compileTime.}=
  node.expectKind {nnkFormalParams,nnkProcDef}
  case node.kind
  of nnkFormalParams:
    return node[0]
  of nnkProcDef:
    return node.params.return_param
  else:
    discard
macro dev_hint(a:untyped):untyped=
  when isMainModule:
    return newCall("hint".ident, a)
  else:
    return newEmptyNode()

proc identdefs_names*(node): seq[NimNode] {.compileTime.}=
  node.expectKind nnkIdentDefs
  result = newSeq[NimNode]()
  for c in 0..node.len-3:
    if node[c].kind == nnkPostfix:
      result.add(node[c][1])
    else:
      result.add(node[c])

proc identdefs_name*(node): NimNode {.compileTime.}=
  node.expectKind nnkIdentDefs
  result = node[node.len-3]
  if result.kind == nnkPostfix:
    result = result[1]
proc identdefs_type*(node): NimNode {.compileTime.}=
  node.expectKind nnkIdentDefs
  result = node[node.len-2]
proc identdefs_default*(node): NimNode {.compileTime.}=
  node.expectKind nnkIdentDefs
  result = node[node.len-1]
proc generic_params*(node):NimNode{.compileTime.}=
  node.expectKind nnkProcDef
  return node[2]

proc `identdefs_type=`*(node,value) {.compileTime.}=
  node.expectKind nnkIdentDefs
  node[node.len-2]=value
proc `identdefs_name=`*(node,value) {.compileTime.}=
  node.expectKind nnkIdentDefs
  if node[node.len-3].kind==nnkPostfix:
    node[node.len-3][1]=value
  else:
    node[node.len-3]=value

proc `identdefs_default=`*(node,value) {.compileTime.}=
  node.expectKind nnkIdentDefs
  node[node.len-1]=value
proc `return_param=`*(node,value) {.compileTime.}=
  node.expectKind {nnkFormalParams,nnkProcDef}
  value.expectKind nnkIdentDefs
  case node.kind
  of nnkFormalParams:
    node[0]=value
  of nnkProcDef:
    node.params.return_param=value
  else:
    discard
proc `generic_params=`*(node,value){.compileTime.}=
  node.expectKind nnkProcDef
  value.expectKind nnkGenericParams
  node[2]=value
proc walk(self:NimNode,kind:NimNodeKind):NimNode=
  var
    cs = @[@[self]]
  while cs.len>0:
    for c in pop(cs):
      if c.kind == kind:
        return c
      cs.add(toSeq(c.children))
proc contains(self:NimNode,value:NimNode):bool=
  result= false
  for n in self:
    if n==value:
      return true
proc remove(frm:NimNode,val:any)=
  frm.del(frm.find(val))
proc createProcHead(source: NimNode):NimNode=
  source.expectKind RoutineNodes
  result = source.copy()
  result.body = newEmptyNode()
proc generateConstructor(
    InitProc:NimNode,
    BaseNewCall:NimNode,
    ):NimNode=
    # tuple[
    #   # head:NimNode,
    #   constr:NimNode,
    #   init:NimNode
    #   ]=
  # dev_hint astGenRepr InitProc
  var T = InitProc.params[1].identdefs_type
  T.expectKind {nnkIdent}
  InitProc.expectKind RoutineNodes
  
  var r = "result".ident
  var init_call = newCall(newDotExpr(r,InitProc.name,))
  var Constr=newProc(
    newIdentNode("new"& $T),
    [T],
    newStmtList(
      newAssignment(
        "result".ident,
        BaseNewCall
      ),
      init_call
    )
  )
  if InitProc.kind==nnkPostfix:
    Constr.name=Constr.name.postfix("*")
  if InitProc[0].kind==nnkPostfix:
    Constr.name = Constr.name.postfix("*")
  
  InitProc.return_param.expectKind nnkEmpty
  InitProc.params.expectMinLen 2
  for i in 2 ..< InitProc.params.len:
    var p = InitProc.params[i]
    Constr.params.add p
    init_call.add p.identdefs_name
  
  result = Constr
  result.expectKind nnkProcDef
  # (
  #   # head: ProcHead,
  #   constr: Constr,
  #   init: InitProc
  # )
  # dev_hint repr result
macro gen_constructor*(stmt_list:untyped):untyped=
  var InitProc = stmt_list
  stmt_list.expectKind {nnkStmtList, nnkProcDef}
  if stmt_list.kind==nnkStmtList:
    stmt_list.expectLen 1
    InitProc = stmt_list[0]
  InitProc.params.expectMinLen 1
  var 
    gen=generateConstructor(
      InitProc, 
      newCall(
        "new".ident, 
        newCall(
          "type".ident, 
          "result".ident) 
      )
    )

  result = newStmtList(createProcHead(InitProc),gen,InitProc)
proc processClassHeader(header:NimNode):tuple[name,root:NimNode,exported:bool]=
  var 
    name=header
    root="RootObj".ident
    exported=false
  
  if header.kind == nnkInfix:
    if $header[0]=="*":
      assert $header[2][0]=="of"
      name = header[1]
      root = header[2][1]
      exported = true
    elif $header[0]=="of":
      name = header[1]
      root = header[2]
      exported= exported
    else:
      error("wrong infix expr", header)
  else:
    exported = true
  return (
    name: name, 
    root: root, 
    exported: exported )
proc objectTy(node:NimNode):NimNode=
  node.expectKind nnkTypeDef
  result = node[2]
  if result.kind == nnkRefTy:
    result = result[0]
  result.expectKind nnkObjectTy
proc typeDefIdent(node:NimNode):NimNode=
  node.expectKind nnkTypeDef
  dev_hint astGenRepr node
  result = node
  result = result[0]
  if result.kind==nnkPragmaExpr:
    result = result[0]
  if result.kind==nnkPostfix:
    result = result[1]
  dev_hint astGenRepr result
  result.expectKind nnkIdent
proc reclist(node:NimNode):NimNode=
  result = node.objectTy[2]
proc typeDefRoot(node:NimNode):NimNode=
  result = node.objectTy[1][0]
  
  
var constructor_regs {.compileTime.} = newTable[
  string,
  tuple[
    typedef: NimNode, 
    baseconstr:NimNode, 
    constrs: seq[tuple[
      head, constr, init: NimNode]]]
]()

proc getInheritedReclist(key:string):NimNode=
  var base = constructor_regs[key]
  result = base.typedef.reclist
  if constructor_regs.contains($base.typedef.typedefRoot):
    for m in getInheritedReclist($base.typedef.typedefRoot):
      result.add(m)

# proc addToConstructorReg(key,val:NimNode)=
#   for c in constructor_regs:
#     c.expectKind nnkStmtList
#     if c[0]==key:
#       c.add(val)
#       return
#   error("Constructor is not registerered")
proc sharesNames(n,b:NimNode):bool=
  var a = n
  if a.kind == nnkIdent:
    a = newIdentDefs(a,newEmptyNode())
  a.expectKind nnkIdentDefs
  b.expectKind nnkIdentDefs
  for ai in 0 ..< a.len-2:
    var ka = a[ai]
    for bi in 0 ..< b.len-2:
      var kb = b[bi]
      if ka==kb: return true
  return false

type 
  TypeDefResult = tuple[
    typesection,
    basenew,
    pre,
    main:NimNode]
  TypeSectionResult = seq[TypeDefResult]
proc class_def(header:NimNode,content:NimNode):TypeDefResult=
  dev_hint astGenRepr header
  dev_hint astGenRepr content
  #NOTE postfix export designation `*` doesn't work yet
  var
    Name,Root:NimNode
    exported:bool
  # echo repr processClassHeader(header)
  (Name,Root,exported) = processClassHeader(header)
  # dev_hint astGenRepr Name
  # dev_hint astGenRepr Root
  
  var
    Main            = newStmtList()
    Pre             = newStmtList()
    This            = "self"
    RecList         = newNimNode(nnkRecList)
    BaseNewName     = ("basenew_"& $Name).ident
    BaseNewCall     = newCall(BaseNewName)
    TypeDef         = 
      nnkTypeDef.newTree(
        Name.postfix("*"),
        # nnkPragmaExpr.newTree(
        #   Name.postfix("*"),
        #   nnkPragma.newTree(
        #     "inject".ident
        #   )
        # ),
        newEmptyNode(),
        nnkRefTy.newTree(
          nnkObjectTy.newTree(
            newEmptyNode(),
            nnkOfInherit.newTree(Root),
            RecList
          )
        )
      )
    TypeSection     = nnkTypeSection.newTree(TypeDef)
    Constrs           = newSeq[tuple[head, constr, init: NimNode]]()

    inherits_class  = constructor_regs.contains($Root)
    inheritReclist  = 
      if constructor_regs.contains($Root): 
        getInheritedReclist($Root) 
      else: 
        nnkRecList.newTree()
    BaseConstructor     = 
      if inherits_class: 
        constructor_regs[$Root].baseconstr.copy()
      else: 
        nnkObjConstr.newTree(newEmptyNode())
  BaseConstructor[0] = Name
  if inherits_class:
    for creg in constructor_regs[$Root].constrs:
      var n_init = creg.init.copy()
      n_init.params[1].identDefs_type=Name
      n_init.params[0]=newEmptyNode()
      var gen = generateConstructor(n_init,BaseNewCall)
      var head = createProcHead(n_init)
      Pre.add head
      Main.add gen
      # gen.addPragma("inject".ident)
      Main.add n_init
      Constrs.add (
        head: head, 
        constr: gen, 
        init: n_init
        )

  # dev_hint astGenRepr Root.base()#.getTypeImpl()
  # BaseConstructor.add(newColonExpr(n.identdefs_name,n.identdefs_default))
  # BaseNew.addPragma("inject".ident)
  proc NewVar(n:NimNode)=
    # dev_hint astGenRepr n
    var v = n.copy()
    v.expectKind nnkIdentDefs
    v.expectMinLen 3
    if v.identdefs_default.kind!=nnkEmpty:
      var d=v.identdefs_default
      v.identdefs_default=newEmptyNode()
      if v.identdefs_type.kind == nnkEmpty:
        v.identdefs_type=nnkTypeOfExpr.newTree(d)
      #Check if in inherited constructor:
      for i in 1 ..< BaseConstructor.len:
        var c = BaseConstructor[i]
        dev_hint astGenRepr c[0]
        dev_hint astGenRepr v.identdefs_name
        dev_hint $($c[0] == $v.identdefs_name)
        if $c[0] == $v.identdefs_name:
          v.expectLen 3
          # Is already in inherited base constructor, overwrite
          BaseConstructor.del(i)
          break
      # Is a new constructor argument
      BaseConstructor.add(
        newColonExpr(
          v.identdefs_name,
          d))
    #Check if in inherited reclist
    for i,m in inheritReclist:
      m.expectKind nnkIdentDefs
      if sharesNames(m,v):
        return
    RecList.add(v)
  proc InjectThisParam(n:NimNode)=
    # inject `This: T` into the arguments
    n.expectKind RoutineNodes
    n.params.expectMinLen 1
    if n.params.kind != nnkFormalParams:
      n.params = newNimNode nnkFormalParams
    if( n.params.len >= 2 and 
        $n.params[1].identdefs_name == This ):
      doAssert(
        (n.params[1].identdefs_type.kind == nnkEmpty or
        n.params[1].identdefs_type == Name),
        "`self` type doesn't match containing `class`\n" & $n.params[1] & "\n" & $Name
      )
      n.params.del(1)
    n.params.insert(1, newIdentDefs(This.ident, Name))
  proc NewThisPragma(n:NimNode)=
    # dev_hint astGenRepr n 
    n.expectLen(1)
    n[0].expectKind(nnkExprColonExpr)
    if not($n[0][0] == "this"):
      error("Only `this` pragma is allowed in class body." & $n[0][0], n[0][0])
    n[0][1].expectKind(nnkIdent)
    Main.add n
    This = $n[0][1]
  proc NewRoutine(n:NimNode)=
    if n.pragma.kind==nnkEmpty:
      n.pragma=newNimNode(nnkPragma)
    # NOTE can't accurately detect base methods yet.
    # if n.kind == nnkMethodDef:
    #   if not n.pragma.contains("base".ident):
    #     n.pragma.add "base".ident
    # NOTE removing inject pragmas
    # n.addPragma("inject".ident)
    var head = createProcHead(n)
    Pre.add head
    if n.name == "init".ident:
      var gen = generateConstructor(n, BaseNewCall)
      for creg in Constrs:
        hint astGenrepr creg.head
        hint astGenrepr head
        # block scope_a:
        # if creg.head == head:
        block scope:
          if creg.head.params.len!=head.params.len:
            break
          for i in 1..<creg.head.params.len:
            if creg.head.params[i][1]!=head.params[i][1]:
              break scope
          Pre.remove(creg.head)
          Main.remove(creg.constr)
          Main.remove(creg.init)
          # break
      Constrs.add (
        head: head, 
        constr: gen,
        init: n
        )
      # gen.addPragma("inject".ident)
      Main.add gen
    n.pragma = newEmptyNode()
    Main.add n
  
  for n in content.copy():
    case n.kind
    of nnkInfix:
      n.expectLen 3
      dev_hint astGenRepr n
      case $n[0]
      of "*=":
        NewVar newIdentDefs(n[1],newEmptyNode(),n[2])
      of "*:":
        NewVar newIdentDefs(n[1],n[2]) 
      else:
        error("invalid class body infix node " & $n.kind,n)

      # NewVar()
      # content.insert(0,nnkVarSection(newIdentDefs(n[1],n[2])))
    of nnkVarSection:
      for c in n: # var f,g,h : t = v
        NewVar c
    of nnkPragma:
      NewThisPragma n
    of nnkMethodDef, nnkProcDef:
      InjectThisParam n
      NewRoutine n
    of nnkIteratorDef, nnkConverterDef, nnkMacroDef, nnkTemplateDef:
      InjectThisParam n
      Pre.add n
    of nnkDiscardStmt: # Valid
      Main.add n
    else:
      dev_hint astGenRepr n
      error("invalid class body node " & $n.kind,n)
  var BaseNew = 
    newProc(
      BaseNewName.postfix("*"),
      [Name],
      newStmtList(
        
        newCall(
          newDotExpr("system".ident,"echo".ident),
          newLit("Base new called " & $BaseNewName)
        ),
        newAssignment(
          "result".ident,
          BaseConstructor
        )
      )
    )
  result = (
    typesection: TypeSection, 
    basenew: BaseNew,
    pre: Pre,
    main: Main,
  )
  # dev_hint astGenRepr quote do:
  #   type X=ref object of RootObj
  #     ## ASDAs
  #     ## asdasd
  #     x*:int
  #     y*,z*:float
  constructor_regs[$Name]=(typedef:TypeDef, baseconstr:BaseConstructor, constrs:Constrs)
  # dev_hint astGenRepr result
  # dev_hint repr result
proc processSectionChunk(source:NimNode):tuple[header:NimNode,content:NimNode]=
  var content = source.copy()
  var header = source.copy()
  if header.kind==nnkInfix:
    if header.len>3:
      header.del(3)
    content = content[3]
  
  return (header: header, content: content)
proc class_section(content: NimNode): TypeSectionResult =
  result = @[]
  for c in content:
    if c.kind in {nnkPragma,nnkTypeSection}:
      result.add((c,nil,nil,nil))
    else:
      var g = processSectionChunk(c)
      dev_hint astGenrepr g.header
      dev_hint astGenrepr g.content
      var v = class_def(g.header,g.content)
      result.add v
      # clssection.add v[0]
      # for i in 1..<v.len:
      #   body.add v[i]
    # return newStmtList(
    #   clssection,
    #   body
    # )
  
proc newPragma(content:varargs[NimNode]):NimNode=
  return nnkPragma.newTree(content)
proc newPragma(content:string):NimNode=
  return newPragma(content.ident)
macro class*(header,content:untyped):typed=
  dev_hint astGenRepr header
  dev_hint astGenRepr content
  result = newStmtList()
  for k,v in class_def(header,content).fieldPairs:
    result.add newCommentStmtNode(k)
    result.add v
  dev_hint repr result
  
macro class*(content:untyped):typed=
  dev_hint astGenRepr content
  var
    typeSection = nnkTypeSection.newTree()
    main = newStmtList()
  result = newStmtList(
    newCommentStmtNode("[START GENERATED CODE]"),
    newPragma("push"),
    # nnkPragma.newTree(
    #   nnkExprColonExpr.newTree(
    #     newIdentNode("this"),
    #     newIdentNode("self")
    #   )
    # ),
    newCommentStmtNode("# Types"),
    typeSection,
    newCommentStmtNode("# Routines"),
    main,
    newPragma("pop"),
    newCommentStmtNode("[END GENERATED CODE]"),
    )
  
  for v in class_section(content):
    main.add("push".newPragma)
    main.add(newCommentStmtNode(
      "## " & $v.typesection[0].typeDefIdent))
    for k,b in fieldPairs(v):
      # dev_hint repr b
      if b!=nil:
        if k=="typesection":
          b[0].expectKind nnkTypeDef
          typeSection.add(b[0])
        else:
          main.add(newCommentStmtNode(
            "### " & $v.typesection[0].typeDefIdent & " " & k))
          main.add(b)
    main.add("pop".newPragma)
  # hint astgenrepr result
  # hint repr result
  dev_hint repr result

when isMainModule:
  # TODO Concept for classes
  # TODO Object Variants for classes 
  # TODO test inheritance
  # TODO typesection in class section
  class: C of RootObj:
    var foo* : int
  class: 
    type I = float
    
    A* of RootObj:
      var
        asdasd: I
        a = 3
        c* = 5
        x,y,u : int
      proc init*(bbdfgdfg: int) =
        echo bbdfgdfg
      proc init*() = discard
      method m*(){.base.}=
        echo "a"
        discard
        ## Hello!!!
    B* of A:
      method m*()=
        echo "b"
        discard
      var 
        a = 1321
        other : A
      proc init*()= discard
  var a = newA(1231231)
  echo a.a
  var b = newB()
  echo b.a == 1321
  b.m()
