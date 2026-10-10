import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionPolynomial

namespace OAI

/-! # Absorbing the actual correction parameter costs into a small power -/

namespace Ostmann

theorem quadratic_original_power_cost {η X R N K : ℝ} (hη : 0 ≤ η) (hX : 1 ≤ X)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hK : 0 ≤ K) (hRX : R ≤ X) (hNR : N ≤ R) (hKX : K ≤ X ^ 3) :
    (X ^ η) ^ 3 * K ^ η * ((2 * R) ^ 2) ^ η * ((2 * R) ^ η) ^ 2 *
      (4 * K * N) ^ η * (2 * R) ^ η ≤ 4 ^ (9 * η) * X ^ (36 * η) := by
  let Y := 4 * X ^ 4
  have hX₀ : 0 ≤ X := by linarith
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hX₁₄ : X ≤ X ^ 4 := by simpa using pow_le_pow_right₀ hX (by norm_num : 1 ≤ (4 : ℕ))
  have hX₂₄ : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hX₃₄ : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hXY : X ≤ Y := by dsimp [Y]; nlinarith [pow_nonneg hX₀ 4]
  have hKY : K ≤ Y := by dsimp [Y]; nlinarith [pow_nonneg hX₀ 4]
  have hRY : 2 * R ≤ Y := by dsimp [Y]; nlinarith [pow_nonneg hX₀ 4]
  have hR₂Y : (2 * R) ^ 2 ≤ Y := by
    have hs : R ^ 2 ≤ X ^ 2 := by gcongr
    dsimp [Y]
    nlinarith
  have hKNY : 4 * K * N ≤ Y := by
    calc
      _ ≤ 4 * X ^ 3 * X := by gcongr; exact hNR.trans hRX
      _ = Y := by dsimp [Y]; ring
  have hpX := Real.rpow_le_rpow hX₀ hXY hη
  have hpK := Real.rpow_le_rpow hK hKY hη
  have hpR := Real.rpow_le_rpow (by positivity : 0 ≤ 2 * R) hRY hη
  have hpR₂ := Real.rpow_le_rpow (sq_nonneg (2 * R)) hR₂Y hη
  have hpKN := Real.rpow_le_rpow (by positivity : 0 ≤ 4 * K * N) hKNY hη
  calc
    _ ≤ (Y ^ η) ^ 3 * Y ^ η * Y ^ η * (Y ^ η) ^ 2 * Y ^ η * Y ^ η := by gcongr
    _ = (Y ^ η) ^ 9 := by ring
    _ = Y ^ (η * 9) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY]
      norm_num
    _ = 4 ^ (9 * η) * X ^ (36 * η) := by
      dsimp [Y]
      rw [Real.mul_rpow (by norm_num) (pow_nonneg hX₀ 4)]
      congr 1
      · congr 1; ring
      · rw [← Real.rpow_natCast, ← Real.rpow_mul hX₀]
        congr 1
        ring

end Ostmann

end OAI
