import OAI.NumberTheory.Ostmann.ZeroDensity.DensityBalanceParameters

namespace OAI

/-! # The balanced exponent and logarithms in the polynomial alternative -/

namespace Ostmann

 theorem density_balance_at_most (σ : ℝ) (hσ : σ ≤ 1) :
    densityBalanceExponent σ ≤ 3 / 2 := by
  unfold densityBalanceExponent
  apply (div_le_iff₀ (by linarith : 0 < 2 * (2 - σ))).mpr
  linarith

 theorem density_target_at_least (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    2 - 2 * σ ≤ densityTargetExponent σ := by
  unfold densityTargetExponent
  apply (le_div_iff₀ (by linarith : 0 < 2 - σ)).mpr
  nlinarith [mul_nonneg (show 0 ≤ σ - 1 / 2 by linarith) (show 0 ≤ 1 - σ by linarith)]

 theorem density_polynomial_balanced_powers (B X σ : ℝ) (hB : 1 ≤ B) (hBX : B ≤ X)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    (B ^ densityBalanceExponent σ) ^ (2 - 2 * σ) + B * X ^ (1 - 2 * σ) ≤
      2 * B ^ densityTargetExponent σ := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have he : (B ^ densityBalanceExponent σ) ^ (2 - 2 * σ) = B ^ densityTargetExponent σ := by
    rw [← Real.rpow_mul hBp.le]
    congr 1
    unfold densityBalanceExponent densityTargetExponent
    have hd : 2 - σ ≠ 0 := by linarith
    field_simp [hd]
  have hx := Real.rpow_le_rpow_of_nonpos hBp hBX (by linarith : 1 - 2 * σ ≤ 0)
  have hb : B * B ^ (1 - 2 * σ) = B ^ (2 - 2 * σ) := by
    rw [show 2 - 2 * σ = 1 + (1 - 2 * σ) by ring, Real.rpow_add hBp, Real.rpow_one]
  have ht := Real.rpow_le_rpow_of_exponent_le hB (density_target_at_least σ hσ hσ1)
  rw [he]
  have h := (mul_le_mul_of_nonneg_left hx hBp.le).trans (hb.le.trans ht)
  linarith

 theorem density_balanced_log_cost (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ) (hT : 2 ≤ T)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    1 + Real.log (2 * (((Q : ℝ) ^ 2 * T) ^ densityBalanceExponent σ) + 1) ≤
      8 * Real.log ((Q : ℝ) * T) := by
  let B := (Q : ℝ) ^ 2 * T
  let L := Real.log ((Q : ℝ) * T)
  let Y := B ^ densityBalanceExponent σ
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hBp : 0 < B := by linarith
  have hY : 2 ≤ Y := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ B)
      (density_balance_at_least_one σ hσ hσ1)
    rw [Real.rpow_one] at h
    exact hB.trans h
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by nlinarith)
  have hlogB := density_conductor_height_log Q hQ T hT
  have hlogY : Real.log Y ≤ 3 * L := by
    rw [show Real.log Y = densityBalanceExponent σ * Real.log B by exact Real.log_rpow hBp _]
    have ha := density_balance_at_most σ hσ1
    have hlB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    have hm := mul_le_mul_of_nonneg_right ha hlB
    dsimp [B, L] at *
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hlog : Real.log (2 * Y + 1) ≤ Real.log 4 + Real.log Y := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by linarith : Y ≠ 0)]
    exact Real.log_le_log (by linarith) (by linarith)
  rw [hlog4] at hlog
  change 1 + Real.log (2 * Y + 1) ≤ 8 * L
  nlinarith [Real.log_two_gt_d9]

end Ostmann

end OAI
