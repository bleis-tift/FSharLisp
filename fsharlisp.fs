let (==) a b = obj.ReferenceEquals(a, b)

let read_line () = System.Console.ReadLine()

let kLPar = '('
let kRPar = ')'
let kQuote = '\''

type obj =
  | Nil
  | Num of int
  | Sym of string
  | Error of string
  | Cons of obj ref * obj ref
  | Subr of (obj -> obj)
  | Expr of obj * obj * obj

let safeCar = function
  | Cons(a, d) -> !a
  | _ -> Nil

let safeCdr = function
  | Cons(a, d) -> !d
  | _ -> Nil

let symTable = ref [("nil", Nil)]
let lookupSym str tbl =
  tbl
  |> List.tryPick (fun (k, v) -> if k = str then Some v else None)
let makeSym str =
  match lookupSym str !symTable with
  | Some sym -> sym
  | None ->
      let ret = Sym str
      symTable := (str, ret)::(!symTable)
      ret

let symQuote = makeSym "quote"
let symIf = makeSym "if"
let symLambda = makeSym "lambda"
let symDefun = makeSym "defun"
let symSetq = makeSym "setq"
let symT = makeSym "t"

let makeCons a d = Cons(ref a, ref d)

let makeExpr args env = Expr(safeCar args, safeCdr args, env)

let rec nreconc tail = function
  | Cons(a, d) as lst ->
      let tmp = !d
      d := tail
      nreconc lst tmp
  | _ -> tail
let nreverse = nreconc Nil

let pairlis lst1 lst2 =
  let rec doit lst1 lst2 acc =
    match lst1, lst2 with
    | Cons(a1, d1), Cons(a2, d2) ->
        doit !d1 !d2 (makeCons (makeCons !a1 !a2) acc)
    | _ -> nreverse acc
  doit lst1 lst2 Nil

let isSpace c =
  c = '\t' || c = '\r' || c = '\n' || c = ' '

let isDelimiter c =
  c = kLPar || c = kRPar || c = kQuote || isSpace c

let skipSpaces (str: System.String) =
  str.TrimStart()

let makeNumOrSym str =
  match System.Int32.TryParse(str) with
  | true, num -> Num num
  | _ -> makeSym str

let position f str =
  str |> Seq.tryFindIndex f

let readAtom (str: System.String) =
  match position isDelimiter str with
  | Some n ->
      (makeNumOrSym (str.Substring(0, n)),
       str.Substring(n, String.length str - n))
  | None -> (makeNumOrSym str, "")

let lookAhead str =
  let str1 = skipSpaces str
  let c = if str1 = "" then '_' else str.[0]
  let rest = if str1 = "" then ""
             else str1.Substring(1)
  (str1, c, rest)

let rec read str =
  let str1, c, rest = lookAhead str
  if str1 = "" then (Error "empty input", "")
  else if c = kRPar then (Error ("invalid syntax: " + str1), "")
  else if c = kLPar then readList rest Nil
  else if c = kQuote then readQuote rest
  else readAtom str1
and readQuote str =
  let elm, next = read str
  (makeCons (makeSym "quote") (makeCons elm Nil), next)
and readList str acc =
  let str1, c, rest = lookAhead str
  if str1 = "" then (Error "unfinished parenthesis", "")
  else if c = kRPar then (nreverse acc, rest)
  else
    match read str1 with
    | Error e, next -> (Error e, next)
    | elm, next -> readList next (makeCons elm acc)

let rec printObj = function
  | Nil -> "nil"
  | Num n -> string n
  | Sym s -> s
  | Error s -> "<error: " + s + ">"
  | Cons _ as obj -> "(" + (printList obj "" "") + ")"
  | Subr _ -> "<subr>"
  | Expr _ -> "<expr>"
and printList obj delimiter acc =
  match obj with
  | Cons(a, d) ->
      printList !d " " (acc + delimiter + printObj !a)
  | Nil -> acc
  | _ -> acc + " . " + printObj obj

let rec findVarInFrame str alist =
  match safeCar (safeCar alist) with
  | Sym k -> if k = str then safeCar alist
             else findVarInFrame str (safeCdr alist)
  | _ -> Nil
let rec findVar sym env =
  match env, sym with
  | Cons(a, d), Sym str ->
      match findVarInFrame str !a with
      | Nil -> findVar sym !d
      | pair -> pair
  | _ -> Nil

let gEnv = makeCons Nil Nil

let addToEnv sym value = function
  | Cons(a, d) -> a := makeCons (makeCons sym value) !a
  | _ -> ()

let updateVar sym value env =
  let bind = findVar sym env
  match bind with
  | Cons(a, d) -> d := value
  | _ -> addToEnv sym value gEnv

let rec eval obj env =
  match obj with
  | Sym _ ->
      match findVar obj env with
      | Nil -> Error ((printObj obj) + " has no value")
      | pair -> safeCdr(pair)
  | Cons _ -> evalCons obj env
  | _ -> obj
and evalCons obj env =
  let opr = safeCar obj
  let args = safeCdr obj
  if opr == symQuote then
    safeCar args
  else if opr == symIf then
    match eval (safeCar args) env with
    | Nil -> eval (safeCar (safeCdr (safeCdr args))) env
    | _ -> eval (safeCar (safeCdr args)) env
  else if opr == symLambda then
    makeExpr args env
  else if opr == symDefun then
    addToEnv (safeCar args) (makeExpr (safeCdr args) env) gEnv
    safeCar args
  else if opr == symSetq then
    let value = eval (safeCar (safeCdr args)) env
    let sym = safeCar args
    updateVar sym value env
    value
  else apply (eval opr env) (evlis args env Nil) env

and evlis lst env acc =
  match lst with
  | Nil -> nreverse acc
  | _ ->
    match eval (safeCar lst) env with
    | Error e -> Error e
    | elm -> evlis (safeCdr lst) env (makeCons elm acc)
and progn body env acc =
  match body with
  | Cons(a, d) -> progn !d env (eval !a env)
  | _ -> acc
and apply f args env =
  match f, args with
  | Error e, _
  | _, Error e -> Error e
  | Subr f1, _ -> f1 args
  | Expr(a, b, e) ,_ -> progn b (makeCons (pairlis a args) e) Nil
  | _ -> Error ((printObj f) + " is not function")

let subrCar args = safeCar (safeCar args)

let subrCdr args = safeCdr (safeCar args)

let subrCons args = makeCons (safeCar args) (safeCar (safeCdr args))

let subrEq args =
  match safeCar args, safeCar (safeCdr args) with
  | Num x, Num y -> if x = y then symT else Nil
  | x, y -> if x == y then symT else Nil

let subrAtom args =
  match safeCar args with
  | Cons _ -> Nil
  | _ -> symT

let subrNumberp args =
  match safeCar args with
  | Num _ -> symT
  | _ -> Nil

let subrSymbolp args =
  match safeCar args with
  | Sym _ -> symT
  | _ -> Nil

let (|ConsDeref|_|) x =
  match x with
  | Cons(a, d) -> Some (!a, !d)
  | _ -> None

let subrAddOrMul f initValue =
  let rec doit args acc =
    match args with
    | ConsDeref(Num num, rest) -> doit rest (f acc num)
    | ConsDeref _ -> Error "wrong type"
    | _ -> Num acc
  fun args -> doit args initValue
let subrAdd = subrAddOrMul (+) 0
let subrMul = subrAddOrMul (*) 1

let subrSubOrDivOrMod f =
  fun args ->
    match safeCar args, safeCar (safeCdr args) with
    | Num x, Num y -> Num (f x y)
    | _ -> Error "wrong type"
let subrSub = subrSubOrDivOrMod (-)
let subrDiv = subrSubOrDivOrMod (/)
let subrMod = subrSubOrDivOrMod (%)

let rec repl prompt =
  printf "%s" prompt
  printfn "%s" (printObj (eval (fst (read (read_line ()))) gEnv))
  repl prompt

let () =
  addToEnv (makeSym "car") (Subr subrCar) gEnv
  addToEnv (makeSym "cdr") (Subr subrCdr) gEnv
  addToEnv (makeSym "cons") (Subr subrCons) gEnv
  addToEnv (makeSym "eq") (Subr subrEq) gEnv
  addToEnv (makeSym "atom") (Subr subrAtom) gEnv
  addToEnv (makeSym "numberp") (Subr subrNumberp) gEnv
  addToEnv (makeSym "symbolp") (Subr subrSymbolp) gEnv
  addToEnv (makeSym "+") (Subr subrAdd) gEnv
  addToEnv (makeSym "*") (Subr subrMul) gEnv
  addToEnv (makeSym "-") (Subr subrSub) gEnv
  addToEnv (makeSym "/") (Subr subrDiv) gEnv
  addToEnv (makeSym "mod") (Subr subrMod) gEnv
  addToEnv (makeSym "t") (makeSym "t") gEnv
  try repl "> " with _ -> ()
