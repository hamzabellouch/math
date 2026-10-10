import OAI.Analysis.IrrationalRotation.Model.ScalarSamplingEstimates
import Mathlib.Tactic

namespace OAI

namespace Invariant233.ScalarSampling

theorem eight_mul_pow_fiftytwo_le_horizon {m : ℕ} (hm : 200 ≤ m) :
    8 * (m : ℝ)^52 ≤ samplingHorizon m := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    8 * (m : ℝ)^52 ≤ (m : ℝ) * (m : ℝ)^52 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (m : ℝ)^53 := by ring
    _ = (m : ℝ)^(53 : ℝ) := (Real.rpow_natCast _ 53).symm
    _ ≤ samplingHorizon m :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem cross_error_scale {m : ℕ} (hm : 200 ≤ m) {N₀ n : ℝ}
    (_hN : 0 < N₀) (hNm : N₀ ≤ (m : ℝ)^2)
    (hn : samplingHorizon m / 2 ≤ n) :
    4 * (N₀ / n) ≤ (m : ℝ)^(-(50 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hQ : 0 < samplingHorizon m := Real.rpow_pos_of_pos hm0 _
  have hn0 : 0 < n := (half_pos hQ).trans_le hn
  have hprod : (4 * N₀) * (m : ℝ)^50 ≤ n := by
    calc
      (4 * N₀) * (m : ℝ)^50 ≤ (4 * (m : ℝ)^2) * (m : ℝ)^50 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNm (by norm_num)) (by positivity)
      _ = 4 * (m : ℝ)^52 := by ring
      _ ≤ samplingHorizon m / 2 := by linarith [eight_mul_pow_fiftytwo_le_horizon hm]
      _ ≤ n := hn
  have hdiv : (4 * N₀) / n ≤ 1 / (m : ℝ)^50 :=
    (div_le_div_iff₀ hn0 (pow_pos hm0 50)).mpr (by simpa using hprod)
  simpa [Real.rpow_neg hm0.le, Real.rpow_ofNat, div_eq_mul_inv, mul_assoc] using hdiv

theorem SamplingPair.first_ge_N₀ {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n') : N₀ ≤ (n : ℝ) := by
  have hmr : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : 2 * (m : ℝ)^2 ≤ samplingHorizon m := by
    calc
      2 * (m : ℝ)^2 ≤ (m : ℝ)^3 := by nlinarith [sq_nonneg (m : ℝ)]
      _ = (m : ℝ)^(3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ ≤ samplingHorizon m :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  linarith [h.N₀_le, h.N_le, h.first_range.1]

end Invariant233.ScalarSampling

end OAI
