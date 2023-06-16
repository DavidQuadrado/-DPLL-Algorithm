(* Abir Bibliotecas *)

open F_parser

(* Leitura de Input *)

let inp = parse "stdin"

let input =
  match inp with 
  |Some a -> a 
  |None -> Var ("")

(* Função que vai tranformar os input e colocar-los em formulas *)

let rec formulaz formula = 
  match formula with
  |True             -> formulaz(Implies(False,False))
  | False           -> And(Not(Var ("t")),Var("t"))
  | Not (a)         -> Not(formulaz a)
  | And (a,b)       -> And(formulaz a, formulaz b )
  | Or (a,b)        -> Or (formulaz a , formulaz b)
  | Implies (a,b)   -> Implies(formulaz a , formulaz b)
  | Equiv (a,b)     -> Equiv( formulaz a, formulaz b)
  | _               -> formula
  
(* Inicio do Algoritmo T *)

(* Código do algoritmo ImpFree *)

let rec impFree formula  = 
  match formula with
  |Not formula1                   -> Not(impFree formula1)
  |Or (formula1,formula2)         -> Or(impFree formula1, impFree formula2)
  |And (formula1,formula2)        -> And (impFree formula1, impFree formula2)
  |Implies (formula1,formula2)    -> Or (Not (impFree formula1), impFree formula2)
  |Equiv (formula1,formula2)      -> And(impFree (Implies(formula1,formula2)),impFree (Implies(formula2,formula1)))
  | _                             -> formula

(* Código do algoritmo NNFC *)

let rec nnfc formula = 
  match formula with
  |Not(Not formula1)               -> nnfc formula1
  |Not(And(formula1,formula2))     -> Or(nnfc (Not formula1), nnfc (Not formula2))
  |Not(Or(formula1,formula2))      -> And(nnfc (Not formula1), nnfc (Not formula2))
  |Or(formula1,formula2)           -> Or((nnfc formula1), (nnfc formula2))
  |And(formula1,formula2)          -> And((nnfc formula1),(nnfc formula2))
  | _                              -> formula

(* Código do algoritmo Distr *)

let rec distr formula1 formula2 =
  match formula1 with 
  |And(formula11,formula12)    -> And(distr formula11 formula2 ,distr formula12 formula2)
  | _                          -> match formula2 with 
                                  |And(formula21,formula22)   -> And(distr formula1 formula21 ,distr formula1 formula22)
                                  | _                         -> Or(formula1,formula2) 

(* Código do algoritmo CNFC *)                                  
                                
let rec cnfc formula = 
  match formula with
  |Or(formula1,formula2)       -> distr (cnfc formula1) (cnfc formula2)
  |And(formula1,formula2)      -> And(cnfc formula1,cnfc formula2)
  | _                          -> formula

(* Fim do Algoritmo T*)

(*-------------------*)

(* Transformar as Formulas FNC em cláusulas  para depois o transformador as juntar numa lista de cláusulas*)

let rec criaClausulas formula =
  match formula with
  | Or(formula1, formula2)  ->  List.append (criaClausulas(formula1)) (criaClausulas(formula2))
  | _                       -> [formula]

(*Junta as cláusulas fornecidas pela função criaCláusulas*)

let rec transformador formula = 
  match formula with
  | And(formula1, formula2) -> List.append (transformador(formula1)) (transformador(formula2))
  | _                       -> [criaClausulas(formula)]

(*-------------------*)

(* Simplificação de S da assunção de l é válido -> S|l ≜ {c \ {−l} | c ∈ S e l ̸∈ c} *)

(* Função para o -l *)

let oposto formula = nnfc(Not(formula))

(* Função que vai remover o literal l *)

let removerClausulaL formula literal = 
  let (aux, _ ) = (List.partition (fun a -> not (List.exists(fun b -> ( b = literal)) a  ) ) formula) in aux 

(* Função que vai retirar as todas as cláusulas o -l *)

let rec filtrarNaoL formula literal =
  match formula with  
  |[] -> [] 
  |clausula :: list_clausulas -> let ( _ , aux) = (List.partition (fun a -> a = (literal)) clausula) in (aux :: (filtrarNaoL list_clausulas literal)) 

(* Função S|l ≜ {c \ {−l} | c ∈ S e l ̸∈ c} *)

let retirarL formula literal = filtrarNaoL (removerClausulaL formula literal) (oposto literal)

(* Função que vai escolher um literal l qualquer *)
let rec escolheL formula_lst lst =
  match formula_lst with
  | []                       -> ( Var(""), [])
  | literal :: list_literais -> if(( match(List.find_opt (fun l -> l = literal) lst) with
                                    | Some a -> a
                                    | _      -> Var("")) <> literal) then (literal, literal::lst) else escolheL (list_literais) lst
(*-------------------*)

(* Inicio do unit_propagate *)

(*Função que vai informar o unit_propagate que tem uma cláusula vazia*)

let clausulaVazia formS = let (a,b) = List.partition (fun a -> (List.length a) = 0 ) formS in 
  if (List.length a) >= 1 then true else false

(* Função que vai procurar uma cláusula unitária *)

let rec unitario formS = 
  match formS with
  | [] -> Var("")
  | clausula :: list_clausulas -> if((List.length clausula) = 1) then (List.hd clausula) else unitario(list_clausulas)

(* Código da função unit_propagate*)

let unit_propagate formS =
  let setForm = [|formS|] in
  let literal = [|unitario(setForm.(0))|] in 
  while((literal.(0) <> Var("")) && (not (clausulaVazia(setForm.(0))))) do 
  setForm.(0) <- (retirarL (setForm.(0)) (literal.(0))) ;
  literal.(0) <- (unitario(setForm.(0)));
  done;
  setForm.(0)

(*-------------------*)

(* Algoritmo Dpll *)

let dpll formS =
  let rec dpll_aux formS listOfUsed =
   let aux_formS = [|unit_propagate(formS)|] in
    if( aux_formS.(0) = []) then   "SAT"  else
    if( clausulaVazia(aux_formS.(0)) ) then "UNSAT"
    else ( 
    let (literal, listOfUsedL) = escolheL ( List.flatten ( aux_formS.(0))) listOfUsed in
    if((dpll_aux (retirarL (aux_formS.(0)) literal) listOfUsedL) = "SAT") then ( "SAT" )
    else ((dpll_aux (retirarL  (aux_formS.(0)) (oposto(literal))) listOfUsedL)))
  in dpll_aux formS []


(* Output *)

let  algoritmoT = cnfc(nnfc(impFree(formulaz(input))))

let algoritmoComClausulas = transformador(algoritmoT)

let algoritmoDpll = dpll (algoritmoComClausulas)

let () = Printf.printf "%s\n" algoritmoDpll 

(* Compilar : ocamlc -I f_parser/ f_parser.cma ProblemaB.ml -o obs *) 