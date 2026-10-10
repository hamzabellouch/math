import OAI.NumberTheory.JointDickman.Amplification.FiniteEventUnion

namespace OAI

/-! # Nonnegative weights on finite unions -/

namespace JointDickman
open Finset

theorem sum_union_le_nonneg {α : Type*} [DecidableEq α] (S T : Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ S ∪ T, f x) ≤ (∑ x ∈ S, f x)+(∑ x ∈ T, f x) := by
  have h := sum_union_inter (s₁ := S) (s₂ := T) (f := f)
  have hi : 0 ≤ ∑ x ∈ S ∩ T, f x := sum_nonneg (fun x _ => hf x)
  linarith only [h,hi]

theorem sum_biUnion_le_nonneg {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (S : ι → Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ I.biUnion S, f x) ≤ ∑ i ∈ I, ∑ x ∈ S i, f x := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [biUnion_insert,sum_insert hi]
    exact (sum_union_le_nonneg _ _ f hf).trans (add_le_add le_rfl ih)

end JointDickman

end OAI
