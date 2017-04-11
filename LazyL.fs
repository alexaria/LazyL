// lazy lambda calculus interpreter


let charlist_string (charlist : char list) = List.foldBack (fun x y -> string x + y) charlist ""

type Term =
    Var of string
    | Abs of string * Term
    | App of Term * Term
    | Seq
    | TChar of char
    | Unit
    | Putch
    | Abort

type Lexeme =
      Backslash
      | LChar of char
      | LParen
      | RParen
      | Arrow
      | Token of string
      | TUnit
      | End

exception LexError

(* lex : string -> (Lexeme list) option *)

let lex s = let s1 = List.ofSeq s in
               let rec lexh st acc =
                        match st with
                        | [] -> List.rev acc
                        | '\\'::rest -> lexh rest (Backslash::acc)
                        | '''::c::'''::rest -> lexh rest (LChar c::acc)
                        | '-'::'>'::rest -> lexh rest (Arrow::acc)
                        | ' '::rest -> lexh rest acc
                        | ';'::';'::rest -> lexh rest (End::acc)
                        | '('::')'::rest -> lexh rest (TUnit::acc)
                        | '('::rest -> lexh rest (LParen::acc)
                        | ')'::rest -> lexh rest (RParen::acc)
                        | c::rest -> let rec many_letters s acc0 =
                                               match s with
                                               | [] -> (List.rev acc0,[])
                                               | c1::r1 -> if System.Char.IsLetter c1
                                                           then many_letters r1 (c1::acc0)
                                                           else (List.rev acc0,s)
                                      in match (System.Char.IsWhiteSpace c, System.Char.IsLetter c) with
                                         | (true,_) -> lexh rest acc
                                         | (_,true) -> let (str,r) = many_letters (c::rest) [] in
                                                          lexh r (Token (charlist_string str) :: acc)
                                         | otherwise -> raise LexError
                   in lexh s1 []

type ParseFragment = PLex of Lexeme | PTerm of Term

exception ParseError

type ParseState = S0 | S1 | S2 | S3

// states:
// S0: need some kind of term
// S2: have a fragment that could already be a complete term
// S1: just read a backslash, need a binder
// S3: just read a binder, need an arrow

let rec parseh state stack input =
  let try_app t cs = match stack with
                     | PTerm t1 :: bs -> parseh S2 (PTerm (App (t1,t)) :: bs) cs
                     | otherwise -> raise ParseError
  in
    match input with
    | [] -> raise ParseError
    | c::cs -> match (state,c) with
               | (S0,LParen) -> parseh S0 (PLex LParen :: stack) cs
               | (S0,Backslash) -> parseh S1 (PLex Backslash :: stack) cs
               | (S0,Token "putch") -> parseh S2 (PTerm Putch :: stack) cs
               | (S0,Token "abort") -> parseh S2 (PTerm Abort :: stack) cs
               | (S0,Token "seq") -> parseh S2 (PTerm Seq :: stack) cs
               | (S0,Token t) -> parseh S2 (PTerm (Var t) :: stack) cs
               | (S0,TUnit) -> parseh S2 (PTerm Unit :: stack) cs
               | (S0,LChar c) -> parseh S2 (PTerm (TChar c) :: stack) cs
               | (S1,Token t) -> parseh S3 (PLex (Token t) :: stack) cs
               | (S2,LParen) -> parseh S0 (PLex LParen :: stack) cs
               | (S2,RParen) -> match stack with
                                | PTerm t2 :: PLex LParen :: PTerm t1 :: bs -> parseh S2 (PTerm (App(t1,t2)) :: bs) cs
                                | PTerm t :: PLex LParen :: bs -> parseh S2 (PTerm t :: bs) cs
                                | PTerm t2 :: PTerm t1 :: bs -> parseh S2 (PTerm (App (t1,t2)) :: bs) (c::cs)
                                | PTerm t :: PLex Arrow :: PLex (Token v) :: PLex Backslash :: bs -> parseh S2 (PTerm (Abs (v,t)) :: bs) (c::cs)
                                | otherwise -> raise ParseError
               | (S2,End) -> match stack with
                             | PTerm t2 :: PTerm t1 :: bs -> parseh S2 (PTerm (App (t1,t2)) :: bs) (c::cs)
                             | PTerm t :: PLex Arrow :: PLex (Token v) :: PLex Backslash :: bs -> parseh S2 ((PTerm (Abs (v,t))) :: bs) (c::cs)
                             | PTerm t :: [] -> t
                             | otherwise -> raise ParseError
               | (S2,Token "putch") -> try_app Putch cs
               | (S2,Token "abort") -> try_app Abort cs
               | (S2,Token "seq") -> try_app Seq cs
               | (S2,Token t) -> try_app (Var t) cs
               | (S2,TUnit) -> try_app Unit cs
               | (S2,LChar c) -> try_app (TChar c) cs
               | (S3,Arrow) -> parseh S0 (PLex Arrow :: stack) cs
               | otherwise -> raise ParseError

(* parse : String -> Some Term *)

let parse s = parseh S0 [] (lex s)
              
(* pprint : Term -> String *)
let rec pprint = function
                 | Var s -> s
                 | Abs (s,t) -> "(\\" + s + " -> " + pprint t + ")"
                 | App (e1,e2) -> "(" + pprint e1 + " " + pprint e2 + ")"
                 | Seq -> "seq"
                 | Unit -> "()"
                 | TChar c -> "'" + string c + "'"
                 | Abort -> "abort"
                 | Putch -> "putch"

type Denval = Thunk of (unit -> Expval)
and Expval = EUnit
           | EChar of char
           | Funct of (Denval -> Expval)

let print_value e = match e with
                    | EUnit -> printfn "()"
                    | EChar c -> printfn "'%c'" c
                    | Funct f -> printfn "<function>"


exception AppliedNonFunction of string
exception NotImplemented
exception VarOutOfScope of string
exception AbortInterpreter

let rec eval_e t env =
  match t with
  | Var v -> match env v with | Thunk th -> th()
  | Abs (v0,b) -> Funct (fun x -> eval_e b (fun v1 -> if v0 = v1 then x else env v1))
  | App (t1,t2) ->
    match eval_e t1 env with
    | Funct f -> f (Thunk (fun () -> eval_e t2 env))
    | EChar c -> raise (AppliedNonFunction "character")
    | EUnit -> raise (AppliedNonFunction "unit")
  | Seq -> Funct (fun (Thunk t1) -> let e1 = t1 () in Funct (fun (Thunk t2) -> t2 ()))
  | TChar c -> EChar c
  | Putch -> Funct (fun (Thunk s) -> match s () with
                                     | EUnit -> printf "()" ; EUnit
                                     | Funct f -> printf "func" ; EUnit
                                     | EChar c -> System.Console.Write c ; EUnit)
  | Abort -> Funct (fun x -> raise AbortInterpreter)
  | Unit -> EUnit

let eval t = eval_e t (fun v -> raise (VarOutOfScope v))

let pp s = pprint (parse s)

let parse_tests =
    printfn "-- PARSER MACHINERY --"
    printfn "actual: %s" (pp @"\x -> t x;;")
    printfn "should be: \\x -> t x"
    printfn "actual: %s" (pp @"(\x -> f (x x)) (\x -> f (x x));;")
    printfn "should be: %s" @"(\x -> f (x x)) (\x -> f (x x))"
    printfn "actual: %s" (pp @"a b c;;")
    printfn "should be: %s" @"((a b) c)"
    printfn "actual: %s" (pp @"seq (putch 'x') (putch 'y');;")
    printfn "should be: %s" @"seq (putch 'x') (putch 'y');;"

let eval_tests =
    printfn "-- INTERPRETATION MACHINERY --"
    printf "actual run: "
    print_value (eval (parse @"(\x -> (\y -> x)) 'a' 'b';;"))
    printfn "should be: 'a'"

let safe_run th =
  try
    th ()
  with
  | VarOutOfScope v -> printfn "the variable %s was used out of scope" v
  | AppliedNonFunction n -> printfn "applied %s as a function" n
  | NotImplemented -> printfn "used a function that isn't implemented."
  | ParseError -> printfn "could not parse the input."
  | LexError -> printfn "could not lex the input!"

let rec repl () =
  try
    safe_run (fun () ->
              printf "> "
              let tm = parse (System.Console.ReadLine())
              in print_value (eval tm))
    repl ()
  with
  | AbortInterpreter -> ()



let evalstream (instream : System.IO.StreamReader) = print_value (eval (parse (instream.ReadToEnd())))

[<EntryPoint>]
let main argv =
  safe_run (fun () -> parse_tests)
  safe_run (fun () -> eval_tests)
  if Array.length argv > 0 then let instream = new System.IO.StreamReader(argv.[0]) in evalstream instream ; instream.Close() else ()
  repl ()
  0