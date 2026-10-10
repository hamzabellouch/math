import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterCostBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_parameter_Z_pow_bound :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, 1 ≤ Z → Real.log Z ≤ 2 * T →
      (Z : ℝ) ^ 14 ≤ Real.exp (T ^ 2) := by
  filter_upwards [eventually_ge_atTop (28 : ℝ)] with T hT
  intro Z hZ hlog
  have hz : (0 : ℝ) < Z := by exact_mod_cast hZ
  have he : (14 : ℝ) * Real.log Z ≤ T ^ 2 := by nlinarith
  have h := Real.exp_le_exp.mpr he
  simpa only [show (14 : ℝ) = (14 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hz] using h

theorem eventually_grid_dimension_bound :
    ∀ᶠ T : ℝ in atTop, ((2 * gridMomentParameter T) ^ 2 : ℕ) ≤ T ^ (1 / 100000 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_mul_rpow_le_rpow 4 (a := 2 / 1000000) (b := 1 / 100000) (by norm_num)]
    with T hT hpow
  have hf : (gridMomentParameter T : ℝ) ≤ T ^ (1 / 1000000 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hT.le _)
  have hid : (T ^ (1 / 1000000 : ℝ)) ^ 2 = T ^ (2 / 1000000 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    norm_num
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (gridMomentParameter T)) hf 2
  push_cast
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
