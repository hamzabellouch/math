import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeOriginalTrims

namespace OAI

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical
universe u v w z s
variable {I : Type u} {C : Type v}
  (Ω : I → C → Type w)
  (M : ∀ i c, Ω i c → Type z) (left right : ∀ i c t, M i c t → C)
  (enc : ∀ i c t, Option (M i c t))
  {D : Type s} (out : ∀ i c t, M i c t → D)

lemma observe_none_iff_success (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    observe Ω M left right enc out b ω c j = none ↔ successAt Ω M left right enc b ω c j = none := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [successAt, observe, probe, Option.map_eq_none_iff]
    · cases he : enc i c (ω.1 c) with
      | none => simp only [successAt, observe, probe, he, Option.map_none, Option.elim_none]
      | some m =>
        simpa only [successAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp only [successAt, observe, probe, he, Option.map_none, Option.elim_none]
      | some m =>
        simpa only [successAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihr ω.2.2 (right i c (ω.1 c) m) j

lemma context_none_observe (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    contextAt Ω M left right enc b ω c j = none → observe Ω M left right enc out b ω c j = none := by
  induction b generalizing c with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [contextAt, probe, Option.some_ne_none, false_implies]
    · cases he : enc i c (ω.1 c) with
      | none => simp only [contextAt, observe, probe, he, Option.map_none, Option.elim_none, implies_true]
      | some m =>
        simpa only [contextAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihl ω.2.1 (left i c (ω.1 c) m) j
    · cases he : enc i c (ω.1 c) with
      | none => simp only [contextAt, observe, probe, he, Option.map_none, Option.elim_none, implies_true]
      | some m =>
        simpa only [contextAt, observe, probe, he, Option.map_some, Option.elim_some] using
          ihr ω.2.2 (right i c (ω.1 c) m) j

lemma observe_context_coherent (b : BinaryTree I) (ω : Tape Ω b) (c : C) (j : Address b) :
    observe Ω M left right enc out b ω c j ≠ none → contextAt Ω M left right enc b ω c j ≠ none :=
  mt (context_none_observe Ω M left right enc out b ω c j)
end SharpRamseyFive.TreeCodec

end OAI
