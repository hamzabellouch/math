import OAI.NumberTheory.TwoPointCorrelations.MRTBandLogGrowth

namespace OAI

/-! The later-band exponential is much smaller than the remaining
polynomial bin factors, uniformly in the band index. -/

namespace TwoPointCorrelations

lemma mrt_log_later_band_lower (P Q : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q) :
    (k : ℝ) ^ 8 * Real.log Q * Real.log P ≤
      Real.log (mrtBandLower P Q k) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hpow : (k : ℝ) ^ 8 ≤ (k : ℝ) ^ (4 * k) :=
    pow_le_pow_right₀ hk1 (by omega)
  have hq : Real.log Q ≤ Real.log Q ^ (k - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hQ (show 1 ≤ k - 1 by omega)
  simp only [mrtBandLower, Real.log_exp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hpow hq (by linarith) (by positivity)) hP

theorem mrt_later_band_exponential_budget {η P Q : ℝ} (hη : 0 ≤ η)
    (k : ℕ) (hk : 2 ≤ k) (hP : 0 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hbudget : 8192 ≤ η * Real.log Q) :
    2048 * (k : ℝ) ^ 6 * Real.log P ≤
      η * Real.log (mrtBandLower P Q k) / (4 * (k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h1 := mul_le_mul_of_nonneg_left (mrt_log_later_band_lower P Q k hk hP hQ) hη
  have h2 := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ (k : ℝ) ^ 8 * Real.log P by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 4 * (k : ℝ) ^ 2)).mpr
  have he : (2048 * (k : ℝ) ^ 6 * Real.log P) * (4 * (k : ℝ) ^ 2) =
      8192 * (k : ℝ) ^ 8 * Real.log P := by ring
  rw [he]
  nlinarith

end TwoPointCorrelations

end OAI
