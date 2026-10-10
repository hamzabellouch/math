import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDetectorBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! Numerical Gaussian estimates for the two-torus detector. These estimates
are proved directly and introduce no heat-kernel hypothesis. -/

namespace ForcedComputation.VelocityDetector
open scoped BigOperators

theorem heat_shell_ratio : Real.exp (-(1 / 32 : ℝ)) ≤ 32 / 33 := by
  have h := Real.add_one_le_exp (1 / 32 : ℝ)
  rw [Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  nlinarith

theorem heat_shell_series :
    1 + 8 * (∑' j : ℕ, (j : ℝ) * Real.exp (-(1 / 32 : ℝ)) ^ j) < 10000 := by
  let q : ℝ := Real.exp (-(1 / 32 : ℝ))
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hq : q ≤ 32 / 33 := heat_shell_ratio
  have hq₁ : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq₀]; linarith
  have hr : ‖(32 / 33 : ℝ)‖ < 1 := by norm_num
  have hsum : (∑' j : ℕ, (j : ℝ) * q ^ j) ≤ 1056 := by
    calc
      _ ≤ ∑' j : ℕ, (j : ℝ) * (32 / 33 : ℝ) ^ j :=
        (hasSum_coe_mul_geometric_of_norm_lt_one hq₁).summable.tsum_le_tsum
          (fun j => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq₀ hq j) (Nat.cast_nonneg j))
          (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
      _ = 1056 := by rw [tsum_coe_mul_geometric_of_norm_lt_one hr]; norm_num
  change 1 + 8 * (∑' j : ℕ, (j : ℝ) * q ^ j) < 10000
  linarith

theorem gaussian_time_factor {d t : ℝ} (hd : 0 < d) (ht : 0 < t) :
    t⁻¹ * Real.exp (-(d ^ 2 / (8 * t))) ≤ 8 / d ^ 2 := by
  have he : (d ^ 2 / (8 * t)) * Real.exp (-(d ^ 2 / (8 * t))) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hpos : 0 < d ^ 2 := sq_pos_of_pos hd
  apply (le_div_iff₀ hpos).mpr
  calc
    _ = 8 * ((d ^ 2 / (8 * t)) * Real.exp (-(d ^ 2 / (8 * t)))) := by
      field_simp [ht.ne']
    _ ≤ 8 * 1 := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = 8 := by norm_num

theorem heat_constant_small :
    (8 * 10000 : ℝ) / (4 * Real.pi * (1 / 32) ^ 2) < 1000000000 ∧
    (8 * 10000 : ℝ) / (4 * Real.pi * (1 / 16) ^ 2) < 100000000 := by
  have hp := Real.pi_gt_three
  constructor
  · apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith

end ForcedComputation.VelocityDetector

end OAI
