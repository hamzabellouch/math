import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionPowerCost
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdMainGrowth

namespace OAI

/-! # The actual main-term normalization and its small-power arithmetic cost -/

namespace Ostmann

theorem quadratic_main_power_cost {η X R D K : ℝ} (hη : 0 ≤ η) (hX : 1 ≤ X)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hRX : R ≤ X) (hDR : D ≤ R) (hKX : K ≤ X ^ 3) :
    (K * D ^ 2 * (2 * R)) ^ (2 * η) * D ^ η ≤ 2 ^ (3 * η) * X ^ (36 * η) := by
  have hX₀ : 0 ≤ X := by linarith
  let Y := 2 * X ^ 6
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hb : K * D ^ 2 * (2 * R) ≤ Y := by
    calc
      _ ≤ X ^ 3 * X ^ 2 * (2 * X) := by gcongr; exact hDR.trans hRX
      _ = Y := by dsimp [Y]; ring
  have hDY : D ≤ Y := by
    have hh : X ≤ X ^ 6 := by simpa using pow_le_pow_right₀ hX (by norm_num : 1 ≤ (6 : ℕ))
    dsimp [Y]
    nlinarith [hDR.trans hRX, pow_nonneg hX₀ 6]
  calc
    _ ≤ Y ^ (2 * η) * Y ^ η := mul_le_mul
      (Real.rpow_le_rpow (by positivity) hb (by positivity))
      (Real.rpow_le_rpow hD hDY hη) (Real.rpow_nonneg hD η) (Real.rpow_nonneg hY.le _)
    _ = Y ^ (3 * η) := by rw [← Real.rpow_add hY]; congr 1; ring
    _ = 2 ^ (3 * η) * X ^ (18 * η) := by
      dsimp [Y]
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hX₀ 6)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX₀]
      congr 1
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) (by positivity)

theorem quadratic_main_scale {M R K ξ : ℝ} (hK : 0 < K) :
    Real.sqrt M / Real.sqrt K * (K ^ ξ + 2 * R) =
      Real.sqrt M * K ^ (ξ - 1 / 2) + 2 * (Real.sqrt M * R / Real.sqrt K) := by
  rw [Real.rpow_sub hK, ← Real.sqrt_eq_rpow]
  ring

end Ostmann

end OAI
