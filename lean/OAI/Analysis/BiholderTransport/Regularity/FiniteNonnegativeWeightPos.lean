import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma finite_nonnegative_weight_zero_on_pos {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, f i ≤ 0)
    (hsum : ∑ i, w i * f i = 0) : ∀ i, 0 < w i → f i = 0 := by
  intro i hi
  apply le_antisymm (hf i)
  by_contra! hh
  have hs : (∑ j, w j * f j) < ∑ j ∈ (Finset.univ : Finset ι), (0:ℝ) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_nonpos_of_nonneg_of_nonpos (hw j) (hf j)
    · exact ⟨i,Finset.mem_univ i,mul_neg_of_pos_of_neg hi hh⟩
  simp [hsum] at hs

lemma sum_filter_positive_weights {ι E : Type*} [Fintype ι]
    [AddCommMonoid E] [Module ℝ E] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f : ι → E) :
    ∑ i ∈ (Finset.univ.filter (fun i => 0 < w i)), w i • f i = ∑ i, w i • f i := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < w i
  · simp only [h,ite_true]
  · have hz : w i = 0 := le_antisymm (le_of_not_gt h) (hw i)
    simp [hz]

end WeakMTWTransport
end

end OAI
