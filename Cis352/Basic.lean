-- CIS352 S'25 -- April 22, 2025
-- Notes on Lean
import Mathlib

--
-- Our goal is to give a whirlwind tour of what's possible in
-- lean. We'll boot up with basic concepts like propositions and
-- inductive types, and then quickly jump into

-- ## Table of Contents
-- 1. Propositional Logic & Basic Tactics
-- 2. Simply-Typed Lambda Calculus
-- 3. Induction over ℕ
-- 4. Structures & Abstract Algebra (Monoids, Groups)
-- 5. Topology

-- Excursion 1: Propositional Logic & Basic Tactics

-- Here, we embrace the Curry-Howard Isomorphism: to prove statements
-- like P ∧ Q, what we do is give a proof of P, and a proof of Q.
-- A "proof" sounds like an abstract mathematical thing, but in fact
-- in this case, it is an algebraic data type (in Scheme an S-expression,
-- but in Lean, it's got a richer structure).

-- Let's prove our first theorem:

-- Here we want to pove: ∀ P and Q (propositions), P ∧ Q is true
-- if and only if Q ∧ P is true. This fact is true constructively,
-- in the sense that we can write a proof for it. We will prove
-- the forward direction only for now
def and_P_Q_attempt_0 {P Q : Prop} (pf_P_and_Q : P ∧ Q) : Q ∧ P :=
  sorry

-- We can always use sorry to punt and not define something.
-- Now, let's try again. Just to explain, P and Q are implicit
-- propositions (logical statements, things like ∀x.x+1=1+x).
-- They're in the curly braces so that Lean knows to automatically
-- infer them (otherwise we would have to manually specify them).
-- pf_P_and_Q is a "proof object" for P ∧ Q, which is a piece of data
-- that proves P ∧ Q.
--
-- Recall that P ∧ Q is provable when you can prove both P ∧ Q. Thus,
-- you can see a logical conjuction (computationally) as a pair of
-- proofs of P and proofs of Q.
--
-- To begin, we build logical and (∧) by writing an explicit datatype
--

-- In Lean4, conjunction is actually defined as a type, like this:
section AndExcursion

inductive MyAnd (a b : Prop) : Prop where
  | intro : a → b → MyAnd a b     -- the sole constructor

infixr:35 " myand " => MyAnd      -- binary notation, precedence 35

-- refl 5 is a proof of 5 = 5, which is not the same thing
-- we can write 5 = 7, but we can never prove that
def example_of_my_and : (5 = 5 myand 4 = 4) := MyAnd.intro (refl 5) (refl 4)

#check example_of_my_and

-- Extract the left component of a proof of `a myand b`.
-- P and Q are the implicitly-quantified propositions,
-- and pf is the proof object that carries the proofs
-- of P and Q, which we can harvest by using a match
-- statement and observing the `intro` constructor.
def myAnd.left {P Q : Prop} (pf : P myand Q) : P :=
  match pf with
  | MyAnd.intro ha _ => ha

-- Same thing on the right: P × Q → Q
def myAnd.right {P Q : Prop} (pf : P myand Q) : Q :=
  match pf with
  | MyAnd.intro _ hb => hb

-- Now let's prove P × Q → Q × P
def myAnd.commutes_fwd {P Q : Prop} (pf : P myand Q) : Q myand P :=
  match pf with
  | MyAnd.intro pf_P pf_Q => (MyAnd.intro pf_Q pf_P)

-- So far, we've been using pattern matching to prove things, but
-- there's another, more intuitive way that we can use in Lean:
-- logic programming. Logic programming lets us use a "tactic-based"
-- approach, where we can use various "tactics" to manipulate
-- the proof state.
--
-- The important thing to understand is that these tactics are
-- fundamentally building terms written in this typed Racket-like
-- language (i.e., matching over inductive datatypes). There is nothing
-- the tactics are doing that you could not do yourself, with a
-- bit of extra (perhaps tedious) work.
def myAnd.commutes_fwd_again {P Q : Prop} (pf : P myand Q) : Q myand P :=
  -- I need to proof Q myand P, using P mand Q. What I do is to apply the
  -- the constructor tactic: I will prove Q and P separately, assuming
  -- P myand Q in each goal.
  by
    cases pf with
    | intro pf_P pf_Q =>
      apply MyAnd.intro
      apply pf_Q
      apply pf_P

-- Here, I used the `apply` tactic, which unifies the head of the goal
-- with the conclusion of the function / theorem I apply, and
-- introduces subgoals when necessary.

-- So far, we have not had explicit quantifiers. We have made them
-- implicit, and lean's type inference has done the work for us.
def myAnd.commutes_fwd_quant : ∀ P Q : Prop, P myand Q → Q myand P :=
  by
    -- Now, we have a quantified statement over P, Q, and P myand Q
    -- we need to introduce these variables and ground them so that
    -- we can work with them and build our own proof.
    intro P Q pf_of_P_and_Q
    -- once we've done intros, we can proceed as planned.
    cases pf_of_P_and_Q with
    | intro pf_P pf_Q =>
      apply MyAnd.intro
      apply pf_Q
      apply pf_P
end AndExcursion

-- Excursion 2: Simply-Typed Lambda Calculus as a lean proposition

-- Now, let's start defining the Simply-Typed Lambda Calculus in
-- Lean. We'll take the rules we wrote in class and we'll transliterate
-- them to Lean.
section STLC

-- Our simple types, I omit sum types for now.
inductive SimplTy : Type
  | int : SimplTy
  | bool : SimplTy
  | times : SimplTy → SimplTy → SimplTy
  | arrow : SimplTy → SimplTy → SimplTy

infixr:25 " ⟶ " => SimplTy.arrow   -- right-associative arrow notation

-- Variable names (can switch to De Bruijn later if desired)
abbrev Var := String

-- Terms of STLC
inductive Term : Type
  | var : Var → Term                     -- variables
  | lam : Var → SimplTy → Term → Term    -- λx : T, t
  | app : Term → Term → Term             -- t₁ t₂
  | pair : Term → Term → Term            -- t₁, t₂
  | fst : Term → Term                    -- fst t
  | snd : Term → Term                    -- snd t

open SimplTy Term -- Open up the types so we can use their
                  -- constructors without qualifying them

-- Dirt-simple typing context: simply a list of variables and their
-- associated types (pairs). First variable in the list has
-- precedence. This is very basic, but enough for this class.
def Ctx := List (Var × SimplTy)

-- Lookup a variable in the context
def lookup : Var → Ctx → Option SimplTy
  | _, []          => none
  | x, (y, T) :: Γ => if x = y then some T else lookup x Γ

-- Typing judgment: Γ ⊢ t : T
inductive HasType : Ctx → Term → SimplTy → Prop
  -- The Var rule
  | var {Γ x T} :
      lookup x Γ = some T →
      HasType Γ (var x) T
  | lam {Γ x T₁ t T₂} :
  -- The Lam rule
      HasType ((x, T₁) :: Γ) t T₂ →
      HasType Γ (lam x T₁ t) (T₁ ⟶ T₂)
  | app {Γ t₁ t₂ T₁ T₂} :
  -- The App rule
      HasType Γ t₁ (T₁ ⟶ T₂) →
      HasType Γ t₂ T₁ →
      HasType Γ (app t₁ t₂) T₂
  | pair {Γ t₁ t₂ T₁ T₂} :
  -- The Pair (cons) rule
      HasType Γ t₁ T₁ →
      HasType Γ t₂ T₂ →
      HasType Γ (pair t₁ t₂) (times T₁ T₂)
  -- The Fst (fst, car) rule
  | fst {Γ t T₁ T₂} :
      HasType Γ t (times T₁ T₂) →
      HasType Γ (fst t) T₁
  -- The Snd (snd, cdr) rule
  | snd {Γ t T₁ T₂} :
      HasType Γ t (times T₁ T₂) →
      HasType Γ (snd t) T₂

notation:50 Γ " ⊢ " t " : " T => HasType Γ t T

-- Now, I want to prove that λ x:bool-> x has type bool ⟶ bool
example : [] ⊢ lam "x" bool (var "x") : bool ⟶ bool := by
  apply HasType.lam
  apply HasType.var
  simp! -- Here I use simp! to simplify everything!

example
  : [] ⊢ lam "x" (times int bool) (fst (var "x")) : (times int bool) ⟶ int :=
  -- Now, here, I'm writing out the proof literally using HasType
  HasType.lam
    (HasType.fst
      (HasType.var rfl))


-- Define values
inductive Value : Term → Prop
  | lam {x T t} : Value (lam x T t)
  | pair {v₁ v₂} : Value v₁ → Value v₂ → Value (pair v₁ v₂)

def subst : Var → Term → Term → Term
  | x, v, var y       => if x = y then v else var y
  | x, v, lam y T t   => lam y T (if x = y then t else subst x v t)
  | x, v, app t₁ t₂   => app (subst x v t₁) (subst x v t₂)
  | x, v, pair t₁ t₂  => pair (subst x v t₁) (subst x v t₂)
  | x, v, fst t       => fst (subst x v t)
  | x, v, snd t       => snd (subst x v t)

-- Small-step semantics (call-by-value)
inductive Step : Term → Term → Prop
  | appLam {x T t v} : Value v → Step (app (lam x T t) v) (subst x v t)
  | appFun {t₁ t₁' t₂} : Step t₁ t₁' → Step (app t₁ t₂) (app t₁' t₂)
  | appArg {v t₂ t₂'} : Value v → Step t₂ t₂' → Step (app v t₂) (app v t₂')
  | fstPair {v₁ v₂} : Value v₁ → Value v₂ → Step (fst (pair v₁ v₂)) v₁
  | fstStep {t t'} : Step t t' → Step (fst t) (fst t')
  | sndPair {v₁ v₂} : Value v₁ → Value v₂ → Step (snd (pair v₁ v₂)) v₂
  | sndStep {t t'} : Step t t' → Step (snd t) (snd t')

-- We can state progress and preservation--but we will not prove them, as the proofs are
-- quite involved.

-- Progress Theorem
theorem progress t T ctx (eq: ctx = []) (ht : ctx ⊢ t : T) : Value t ∨ ∃ t', Step t t' := by
  sorry

-- lemma subst_preserves_typing : ∀ {Γ x v t T U}, Γ ⊢ v : U → ((x, U) :: Γ) ⊢ t : T → Γ ⊢ subst x v t : T := sorry

-- Preservation Theorem
theorem preservation {t t' T} (ht : [] ⊢ t : T) (hs : Step t t') : [] ⊢ t' : T := by
  sorry

end STLC

-- Excursion 3: Induction over the naturals

section Induction
  open Nat

  #check succ_add

  lemma add_assoc_nat (m n k : ℕ) : (m + n) + k = m + (n + k) := by
    induction m with
    | zero => simp
    | succ n ih => -- now we get an inductive hypothesis
    simp [ih, succ_add]

end Induction

section Math

-- Excursion 4: Abstract Algebra (from Mathlib)

-- Abstract algebra (monoids and groups)
-- Here we're using Mathlib

--
-- In this section, we explore how Lean4 and Mathlib handle abstract algebraic structures such as monoids and groups. We define a custom structure extending a monoid with a distinguished point.
--
open Group

--
-- Let's recall a fundamental lemma in group theory: the inverse of a product is
-- equal to the product of inverses in reverse order. This lemma is already present
-- in Mathlib (`inv_mul_eq_iff_eq_mul`). We demonstrate how one might prove it directly.
--
lemma inv_mul (G : Type _) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- We use a known lemma from Mathlib that characterizes inverses
  rw [eq_comm]
  apply inv_mul_eq_iff_eq_mul.mpr
  simp

#check inv_mul_eq_iff_eq_mul

lemma inv_mul_direct (G : Type _) [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- We verify the inverse directly by group axioms
  apply inv_eq_of_mul_eq_one_right
  calc
    (a * b) * (b⁻¹ * a⁻¹)
      = a * (b * b⁻¹) * a⁻¹ := by simp [mul_assoc]
    _ = a * 1 * a⁻¹         := by simp
    _ = a * a⁻¹             := by simp
    _ = 1                   := by simp

-- Introductory Topology on `ℝ`

open Topology
open TopologicalSpace
open Real
open Set


-- We first verify a fundamental property: the identity function on the real numbers is continuous.
-- This fact is basic and provided by Mathlib, but here's how one could explicitly prove it.

lemma continuous_id_R : Continuous (fun x : ℝ => x) := by
  -- continuity of identity function is directly known in Mathlib
  simpa using continuous_id

-- Another important property in topology is that standard open intervals (a,b) in ℝ are open sets.

-- The intersection of {x | a < x} and {x | x < b} is an open interval
lemma isOpen_int_two_opens (a b : ℝ) : IsOpen (Ioo a b) := by
  apply IsOpen.inter
  exact (isOpen_lt continuous_const continuous_id)
  exact (isOpen_lt continuous_id continuous_const)

-- The union of the two open intervals (a,b) ∪ (c,d) is open
lemma isOpen_union_Ioo (a b c d : ℝ) :
    IsOpen (Ioo a b ∪ Ioo c d) := by
  apply IsOpen.union
  · exact isOpen_int_two_opens a b
  · exact isOpen_int_two_opens c d

-- Last, let's explore continuity from a topological context, seeing how easy it is to
-- work in a very general domain using mathlib's abstractions.

-- Show that if f(x) = x + c, then the preimage of an open interval under f is open
-- In topology, a function is continuous if the preimage of every open set is open.
-- This generalizes the ε-δ definition from analysis.
lemma preimage_of_Ioo_add (c a b : ℝ) :
    IsOpen ((fun x ↦ x + c) ⁻¹' Ioo a b) := by
  -- First, observe the function is continuous
  have h_cont : Continuous (fun x ↦ x + c) :=
    continuous_id.add continuous_const
  -- Then, apply that the preimage of an open set under a continuous function is open
  exact IsOpen.preimage h_cont (isOpen_int_two_opens a b)

#check preimage_of_Ioo_add
-- ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] {f : α → β},
--   Continuous f → ∀ {s : Set β}, IsOpen s → IsOpen (f ⁻¹' s)

end Math
