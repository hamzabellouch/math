import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
lemma sum_dite_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : ∀ x, P x → M) :
    (∑ x, if h : P x then f x h else 0) = ∑ x : {x // P x}, f x.val x.property := by
  classical
  have he := (Equiv.Set.sumCompl {x | P x}).sum_comp
    (fun x => if h : P x then f x h else 0)
  rw [Fintype.sum_sum_type] at he
  rw [← he]
  simp only [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inr]
  have hp : (∑ x : {x // P x}, if h : P x.val then f x.val h else 0) =
      ∑ x : {x // P x}, f x.val x.property := by
    apply Finset.sum_congr rfl
    intro x _
    exact dite_eq_left x.property
  have hn : (∑ x : {x // ¬P x}, if h : P x.val then f x.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact dite_eq_right x.property
  exact (congrArg₂ (· + ·) hp hn).trans (add_zero _)

end BinaryCoordinateSweeps

end

end OAI
