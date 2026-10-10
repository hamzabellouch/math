import OAI.Geometry.RCD.Metric.VolumeBudget

namespace OAI

/-! # A source budget from an upper volume bound, without profile monotonicity -/

open scoped BigOperators

namespace RegularPointCoordinates

theorem volume_defect_budget_of_uniform_upper {A M : ℕ → ℝ} {C B U : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hupper : ∀ i, A i ≤ U) (hM : ∀ i, 0 ≤ M i)
    (hbound : ∀ i, M i ≤ C * (A (i + 1) - A i) + B * (1 / 4 : ℝ) ^ i) :
    Summable M ∧ (∑' i, M i) ≤ C * (U - A 0) + B * (4 / 3) := by
  have hfinite (k : ℕ) : (∑ i ∈ Finset.range k, M i) ≤ C * (U - A 0) + B * (4 / 3) := by
    have h := Finset.sum_le_sum (s := Finset.range k) (fun i _ => hbound i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      volume_profile_increment_sum] at h
    have hv := mul_le_mul_of_nonneg_left (sub_le_sub_right (hupper k) (A 0)) hC
    have hg := mul_le_mul_of_nonneg_left (sum_range_quarter_pow_le k) hB
    exact h.trans (add_le_add hv hg)
  exact ⟨summable_of_sum_range_le hM hfinite, Real.tsum_le_of_sum_range_le hM hfinite⟩

end RegularPointCoordinates

end OAI
