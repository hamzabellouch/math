import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma finite_nonnegative_weight_exists_ge {ι : Type*} [Fintype ι] [Nonempty ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) {a : ℝ}
    (ha : a ≤ ∑ i, w i * f i) : ∃ i, a ≤ f i := by
  by_contra hn
  have hf : ∀ i, f i < a := by simpa only [not_exists,not_le] using hn
  have hpos : ∃ i, 0 < w i := by
    by_contra hp
    have hz : ∀ i, w i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun h => hp ⟨i,h⟩)) (hw i)
    simp only [hz,Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨j,hj⟩ := hpos
  have hh : (∑ i, w i * f i) < ∑ i, w i * a := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hf i).le (hw i)
    · exact ⟨j,Finset.mem_univ j,mul_lt_mul_of_pos_left (hf j) hj⟩
  rw [← Finset.sum_mul,hsum,one_mul] at hh
  exact (not_lt_of_ge ha) hh

end WeakMTWTransport
end

end OAI
