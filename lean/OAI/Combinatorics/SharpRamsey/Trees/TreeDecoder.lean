import Mathlib

namespace OAI

section
namespace SharpLogRamsey.TreeDecoder
open BinaryTree List
open scoped Classical
noncomputable section
variable {A B I C : Type*}

abbrev Domains (A B : Type*) := Finset A × Finset B

abbrev CapReader (A B C : Type*) := Domains A B → C → Domains A B

def execute (read : CapReader A B C) (choose : I → Domains A B → Option C) :
    BinaryTree I → Domains A B → BinaryTree (I×C)
  | .nil, _ => .nil
  | .node i l r, U => match choose i U with
    | none => .nil
    | some c =>
      let V := read U c
      .node (i,c) (execute read choose l (V.1,U.2))
        (execute read choose r (U.1,V.2))

lemma execute_height (read : CapReader A B C) (choose : I → Domains A B → Option C)
    (t : BinaryTree I) (U : Domains A B) :
    (execute read choose t U).height≤t.height := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [execute]
    split
    · simp
    · simp only [height]
      exact Nat.add_le_add_right (max_le_max (hl _) (hr _)) 1

lemma execute_numNodes (read : CapReader A B C) (choose : I → Domains A B → Option C)
    (t : BinaryTree I) (U : Domains A B) :
    (execute read choose t U).numNodes≤t.numNodes := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [execute]
    split
    · simp
    · simp only [numNodes]
      exact Nat.add_le_add_right (Nat.add_le_add (hl _) (hr _)) 1

def flagDomain (R : A → B → Prop) (U : Domains A B) : Finset (A×B) :=
  (U.1×ˢU.2).filter (fun z => R z.1 z.2)

def retained (R : A → B → Prop) (U : Domains A B) (xs : List (A×B)) (n : ℕ) : List (A×B) :=
  (xs.filter (fun z => z∈flagDomain R U)).take n

lemma retained_sublist (R : A → B → Prop) (U : Domains A B) (xs : List (A×B)) (n : ℕ) :
    retained R U xs n <+ xs :=
  (List.take_sublist n _).trans List.filter_sublist

lemma retained_mem (R : A → B → Prop) (U : Domains A B) (xs : List (A×B)) (n : ℕ)
    {x : A×B} (hx : x∈retained R U xs n) : x∈flagDomain R U := by
  exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_take hx)).2

def output (R : A → B → Prop) (read : CapReader A B C)
    (targets : I → List (A×B)) (counts : I → ℕ) : BinaryTree (I×C) → Domains A B → List (A×B)
  | .nil, _ => []
  | .node (i,c) l r, U =>
    let V := read U c
    output R read targets counts l (V.1,U.2) ++
      retained R V (targets i) (counts i) ++
        output R read targets counts r (U.1,V.2)

def message (R : A → B → Prop) (read : CapReader A B C)
    (targets : I → List (A×B)) (counts : I → ℕ) : BinaryTree (I×C) → Domains A B → BinaryTree (C×ℕ)
  | .nil, _ => .nil
  | .node (i,c) l r, U =>
    let V := read U c
    .node (c,(retained R V (targets i) (counts i)).length)
      (message R read targets counts l (V.1,U.2))
      (message R read targets counts r (U.1,V.2))

def decode (R : A → B → Prop) (read : CapReader A B C) :
    BinaryTree (C×ℕ) → Domains A B → List (Finset (A×B))
  | .nil, _ => []
  | .node (c,n) l r, U =>
    let V := read U c
    decode R read l (V.1,U.2) ++ List.replicate n (flagDomain R V) ++
      decode R read r (U.1,V.2)

lemma forall₂_replicate_membership {α : Type*} (xs : List α) (S : Finset α)
    (h : ∀ x∈xs,x∈S) : List.Forall₂ (fun x D => x∈D) xs (List.replicate xs.length S) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons,List.replicate_succ]
    exact List.Forall₂.cons (h a (by simp))
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem decoder_correct (R : A → B → Prop) (read : CapReader A B C)
    (targets : I → List (A×B)) (counts : I → ℕ) (t : BinaryTree (I×C)) (U : Domains A B) :
    List.Forall₂ (fun x D => x∈D) (output R read targets counts t U)
      (decode R read (message R read targets counts t U) U) := by
  induction t generalizing U with
  | nil => exact List.Forall₂.nil
  | node z l r hl hr =>
    rcases z with ⟨i,c⟩
    simp only [output,message,decode]
    apply List.rel_append
    · apply List.rel_append
      · exact hl _
      · apply forall₂_replicate_membership
        intro x hx
        exact retained_mem R _ _ _ hx
    · exact hr _

def population (targets : I → List (A×B)) : BinaryTree I → List (A×B)
  | .nil => []
  | .node i l r => population targets l ++ targets i ++ population targets r

theorem output_sublist (R : A → B → Prop) (read : CapReader A B C)
    (choose : I → Domains A B → Option C) (targets : I → List (A×B)) (counts : I → ℕ)
    (t : BinaryTree I) (U : Domains A B) :
    output R read targets counts (execute read choose t U) U <+ population targets t := by
  induction t generalizing U with
  | nil => rfl
  | node i l r hl hr =>
    simp only [execute]
    split
    · exact List.nil_sublist _
    · simp only [output,population]
      exact ((hl _).append (retained_sublist R _ _ _)).append (hr _)

end
end SharpLogRamsey.TreeDecoder

end

end OAI
