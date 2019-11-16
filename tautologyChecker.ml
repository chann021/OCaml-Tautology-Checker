(* Sam Channon
   chann021@umn.edu
   10/25/2019
  Project 1 contains type definitions for proposition and conditional, along with
  five functions, ifify, normalize, substitute, simplify and tautology.

  Program does recieve a warning about simplify not being exhaustive for the case of
  (If (If _,_,_), _, _) but of course, this shouldn't matter because normalize handles these
  occurances before simplify is called.
*)

type proposition =
  False |
  True |
  Var of string |
  And of proposition * proposition |
  Or of proposition * proposition |
  Not of proposition |
  Imply of proposition * proposition |
  Equiv of proposition * proposition ;;



type conditional =
  IffyFalse |
  IffyTrue |
  IffyVar of string |
  If of conditional * conditional * conditional ;;


(* Function ifify takes in a proposition type and picks it apart to reassemble it as a conditional
   statement with only if statements, contains 3 base cases to tell the recursion when to stop*)
let rec ifify prop =
  match prop with
    | True -> IffyTrue
    | False -> IffyFalse
    | Var name -> IffyVar name
    | Not rest -> (If ((ifify rest), IffyFalse, IffyTrue))
    | And (left, right) -> (If ((ifify left), (ifify right), IffyFalse))
    | Or (left, right) -> (If ((ifify left), IffyTrue, (ifify right)))
    | Imply (left, right) -> (If ((ifify left), (ifify right), IffyTrue))
    | Equiv (left, right) -> (If ((ifify left), (ifify right),(If ((ifify right), IffyFalse, IffyTrue))))
;;


(* Function normalize takes the newly constructed conditional statement and removes all occurances of an
   if statement being the first argument of another if statement as seen in the 7th match. Creates a conditional
   that is manageable by the function simplify*)
let rec normalize cond =
  match cond with
    | IffyFalse -> IffyFalse
    | IffyTrue -> IffyTrue
    | IffyVar name -> IffyVar name
    | (If (IffyFalse, mid, right)) -> (If (IffyFalse, (normalize mid), (normalize right)))
    | (If (IffyTrue, mid, right)) -> (If (IffyTrue, (normalize mid), (normalize right)))
    | (If (IffyVar name, mid, right)) -> (If (IffyVar name, (normalize mid), (normalize right)))
    | (If (If (left, mid, right), left2, right2)) -> normalize (If ((normalize left), (normalize (If (mid, left2, right2))), (normalize (If (right, left2, right2)))))
;;


(* Function substitute used as a helper function for simplify to swap all occurances of a specific variable with
   a boolean value to determine tautologies*)
let rec substitute c v b =
  match c with
    | IffyFalse -> IffyFalse
    | IffyTrue -> IffyTrue
    | IffyVar name ->
        if name = v then
          b
        else
          IffyVar name
    | (If (left, mid, right)) ->
          (If ((substitute left v b), (substitute mid v b), (substitute right v b)))

;;


(* Function simplify which takes a normalized conditional and tests every variation of true and
   false to essentially make its own virtual truth table to test if all variation are true and if so
   deftermines that the origional proposition is a tautology. If one of the variation tests returns
   false then the proposition is not a tautology*)
let rec simplify cond =
  match cond with
    | IffyFalse -> IffyFalse
    | IffyTrue -> IffyTrue
    | IffyVar name -> IffyVar name
    | (If (IffyTrue, left, right)) -> simplify left
    | (If (IffyFalse, left, right)) -> simplify right
    | (If (v, IffyTrue, IffyFalse)) -> simplify v
    | (If (left, mid, right)) when mid = right -> simplify mid
    | (If (IffyVar left, mid, right)) ->
        if simplify (If( IffyTrue, (substitute mid left IffyTrue), right)) = IffyTrue && simplify (If( IffyFalse, mid, (substitute right left IffyFalse))) = IffyTrue then
          IffyTrue
        else
          IffyFalse
;;


(* Function tautology to check if a proposition is a tautology by calling the functions above
   Returns true when a proposition is a tautology and false when a proposition isn't a tautology*)
let tautology p =
    let condition = ifify p in
    let norm = normalize condition in
    let simple = simplify norm in
      if simple = IffyTrue then
        true
      else
        false
;;


(* Test Cases:

Tautology examples:
Example in project description:*)
tautology (Imply (Not (And (Var "p", Var "q")), Or (Not (Var "p"), Not (Var "q"))));;
(*- : bool = true

Distributivity tautology [P ^ (Q \/ R)] <-> [(P ^ Q) \/ (P ^ R)]:*)
tautology (Equiv (And (Var "p", Or (Var "q", Var "r")), Or (And (Var "p", Var "q"), And (Var "p", Var "r"))));;
(*- : bool = true

Definition of the biconditional (p <-> q) <-> [(p -> q) ^ (q -> p)]:*)
tautology (Equiv (Equiv (Var "p", Var "q"), And (Imply (Var "p", Var "q"), Imply (Var "q", Var "p"))));;
(*- : bool = true

Obvious non-tautology propositions:

p ^ q*)
tautology (And (Var "p", Var "q"));;
(*- : bool = false

~(p ^ q)*)
tautology (Not (And (Var "p", Var "q")));;
(*- : bool = false

(p ^ q) -> ~r*)
tautology (Imply ( And( Var "p", Var "q"), Not (Var "r")));;
(*- : bool = false

Random variation of project example:    ~(p ^ q) -> (~p ^ ~q)*)
tautology (Imply (Not (And (Var "p", Var "q")), And (Not (Var "p"), Not (Var "q"))));;
(*- : bool = false
*)

(*Random edit to definition of biconditional to show the program works with longer non-tautologies
 (p <-> q) <-> [(p -> q) ^ (q \/ p)]*)
tautology (Equiv (Equiv (Var "p", Var "q"), And (Imply (Var "p", Var "q"), Or (Var "q", Var "p"))));;
(*- : bool = false*)
