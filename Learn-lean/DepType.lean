namespace Intro

/- 
 Lean natural numbers are arbitrary precision unsigned integers.
 Type is an abbrev. for Type 0 (universe of types)
-/

constant a : Nat
constant b : Nat

constant f : Nat → Nat
constant t: Nat × Nat
constant T: Prod Nat Nat
constant F: (Nat -> Nat) -> Nat

#check a
#check a + 4
#check f 
#check t.1
#check T.fst
#check F f

#check Nat
#check Nat -> Bool

constant α : Type
constant 𝔽 : Type -> Type

#check 𝔽 α 
#check 𝔽 Bool
#check Prod α Nat 

#check Type
#check List
#check Prod

constant C : Type _
universe U
constant D : Type U
#check C
#check D

-- fn :: a -> a
-- fn a = a
def fn (α : Type _)(a : α) := a
#check fn
end Intro

namespace Fun_Abstraction

#check fun (x: Nat) => x + 5
#check λ (α : Type _) (a: α) => a

constant f : Nat -> Bool -> Bool
constant h : Nat -> Bool
#check fun x y => f x (h y)

/-alpha equivalence-/
constant b: Bool
#check (fun (α β : Type) (b: β) (x: α) => b) Nat Bool 
#reduce (fun (α β : Type) (b: β) (x: α) => b) Nat Bool 
end Fun_Abstraction

/-definitions-/
constant Bar : Nat -> Nat -> Nat
constant x : Nat
constant y : Nat
def bar (x : Nat) (y : Nat) : Nat := x + y

/-this approach of defining functions is better-/
def barr : Nat -> Nat -> Nat :=
  fun x y => x + y

#check Bar
#check Bar x y
#reduce Bar x y
#check bar
#print bar
#eval bar 1 2
#reduce bar

#check barr
#reduce barr 
#eval barr 2 3
#print barr

def f (α : Type u) (β : α -> Type v) (a : α) (b: β a) : (a : α) × β a  := ⟨ a, b ⟩  

#reduce f
#reduce (f Type (fun α => α) Nat 10).2

section 
variable (α β γ : Type)
variable (g: β -> γ) (f: α -> β) (h: α -> α)
variable (x: α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
end

namespace typeclasses

class Add(α : Type) where
  add : α → α → α 

#check @Add.add

constant el : Type u -> Type u
namespace el
universe u

inductive nat: Type u where
| z : nat
| succ : nat -> nat

#check nat.succ nat.z

def add  (a: nat) (b: nat): nat :=
  match a with
  | nat.z => b
  | nat.succ x => nat.succ (add x b)

#reduce add (nat.succ nat.z) (nat.succ nat.z)

constant F : { a : Type u } -> List a -> Type u

constant a : Type v
def b := List (List (Type u))
#check b
#check F
#check F List.nil

universe v
inductive elof (α : Type v): Type v  where
| mk (a : α) : elof α 

def elof.mk1 : {α : Type u} -> { n: List α } -> (b : List (List α)) -> elof (List α) := 
 fun {α} {n} xs => match xs with
 | List.nil => elof.mk n
 | List.cons  _ => elof.mk n
 | List.cons (List.cons a List.nil) _ => elof.mk n

-- #check @elof.mk a
-- #check List.cons
-- #reduce elof.mk1 (List.cons a List.nil : List (Type v))
-- #reduce elof.mk1 (List.nil : List (Type v))

end el

end typeclasses