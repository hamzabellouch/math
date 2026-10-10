import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma filtered_sigma_weight_bound {α : Type*} [Fintype α] {β : α → Type*}
    [∀ a, Fintype (β a)] {B w : ℝ} (hB : 0 ≤ B) (hw : 0 ≤ w) :
    (∑ z : Sigma β, if (Fintype.card (β z.1) : ℝ) ≤ B then w else 0) ≤
      (Fintype.card α : ℝ)*B*w := by
  classical
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ a : α, B*w := by
      apply Finset.sum_le_sum
      intro a _
      by_cases h : (Fintype.card (β a) : ℝ) ≤ B
      · simp only [h,ite_true,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right h hw
      · simp only [h,ite_false,Finset.sum_const_zero]
        exact mul_nonneg hB hw
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end SharpTerminalLeave

end

end OAI
