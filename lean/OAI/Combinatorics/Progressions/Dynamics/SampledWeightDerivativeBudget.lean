import OAI.Combinatorics.Progressions.Estimates.NormalizedSampledHistogram

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

theorem sampledWeightInterpolant_deriv_le (n : ℕ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ n ψ)
    {a S R K B : ℝ} (hK : 0 < K) (hS : 0 < S) (hZ : 0 < sampledWeightSum ψ a S R)
    (hB : ∀ x, |iteratedDeriv n ψ x| ≤ B) (u : ℝ) :
    |iteratedDeriv n (sampledWeightInterpolant ψ a S R K) u| ≤
      (K / sampledWeightSum ψ a S R) * (K / S) ^ n * B := by
  rw [sampledWeightInterpolant_deriv n ψ hψ, abs_mul, abs_mul,
    abs_of_pos (div_pos hK hZ), abs_of_nonneg (pow_nonneg (div_nonneg hK.le hS.le) n)]
  exact mul_le_mul_of_nonneg_left (hB _) (mul_nonneg (div_nonneg hK.le hZ.le)
    (pow_nonneg (div_nonneg hK.le hS.le) n))

theorem sampledWeightInterpolant_normalized_deriv_bound (n : ℕ) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ n ψ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a R K δ B : ℝ} (hR : 0 ≤ R) (hK : 0 < K) (hδ : 0 < δ) (hS : 1 ≤ K * δ)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (hI : 0 < ∫ x, ψ x)
    (hlarge : 2 * ((2 * R + 2) * (L : ℝ)) / (∫ x, ψ x) ≤ K * δ)
    (hB0 : 0 ≤ B) (hB : ∀ x, |iteratedDeriv n ψ x| ≤ B) (u : ℝ) :
    |iteratedDeriv n (sampledWeightInterpolant ψ a (K * δ) R K) u| ≤
      (2 * B / (∫ x, ψ x)) / δ ^ (n + 1) := by
  have hZ := sampledWeightSum_pos ψ hLip (a := a) hR hS hsupport hI hlarge
  have hl := (sampledWeightSum_bounds ψ hLip (a := a) hR hS hsupport hI hlarge).1
  have hKZ : K / sampledWeightSum ψ a (K * δ) R ≤ 2 / ((∫ x, ψ x) * δ) := by
    apply (div_le_div_iff₀ hZ (mul_pos hI hδ)).mpr
    nlinarith
  have hKS : K / (K * δ) = δ⁻¹ := by field_simp
  calc
    _ ≤ (K / sampledWeightSum ψ a (K * δ) R) * (K / (K * δ)) ^ n * B :=
      sampledWeightInterpolant_deriv_le n ψ hψ hK (mul_pos hK hδ) hZ hB u
    _ ≤ (2 / ((∫ x, ψ x) * δ)) * δ⁻¹ ^ n * B := by
      rw [hKS]
      gcongr
    _ = _ := by
      rw [pow_succ, inv_pow]
      field_simp

end Erdos3

end

end OAI
