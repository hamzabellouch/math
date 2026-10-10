import OAI.Analysis.IrrationalRotation.Analysis.ScalarBVDiscrepancy
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEstimates

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarRectangles

private theorem power_error_eq (m : ℕ) :
    29 / (m : ℝ)^80 = 29 * (m : ℝ)^(-(80 : ℝ)) := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [Real.rpow_neg hm0]
  norm_num [Real.rpow_ofNat, div_eq_mul_inv]

theorem specified_separated_estimates : ScalarSampling.AllSeparatedEstimates := by
  refine ⟨29, by norm_num, 200, le_rfl, ?_⟩
  intro m hm N₀ N n n' hp
  have hsep : ∀ i j : ℤ, |i| ≤ (m ^ 300 : ℕ) → |j| ≤ (m ^ 300 : ℕ) →
      (i, j) ≠ (0, 0) →
      N * (m : ℝ)^1000 < |(i : ℝ) * n + (j : ℝ) * n'| := by
    intro i j hi hj hij
    apply hp.separated i j hi hj
    by_contra h
    push Not at h
    exact hij (by simp [h.1, h.2])
  constructor
  · intro a b c d ha hab hb hc hcd hd
    have h := scalar_rectangles_ae m hm N₀ N hp.N₀_pos hp.N₀_le hp.N_le n n'
      hp.first_range.1 hp.second_range.1 hsep a b c d ha hab hb hc hcd hd
      (Ico a b) (Ico c d) Ico_ae_eq_Icc Ico_ae_eq_Icc
    rw [power_error_eq m] at h
    exact h
  · intro f g hf hg
    have h := scalar_bv_discrepancy m hm N₀ N hp.N₀_pos hp.N₀_le hp.N_le n n'
      hp.first_range.1 hp.second_range.1 hsep f g hf hg
    rw [power_error_eq m] at h
    exact h

theorem full_scalar_estimates : ScalarSampling.ScalarSamplingEstimates where
  kernel := ScalarSampling.all_kernel_estimates
  marginal := ScalarSampling.all_marginal_estimates
  separated := specified_separated_estimates

end Invariant233.ScalarRectangles

end

end OAI
