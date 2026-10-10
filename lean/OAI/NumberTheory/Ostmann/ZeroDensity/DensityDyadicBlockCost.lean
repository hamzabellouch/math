import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDivisorBlockSieve

namespace OAI

/-! # The sharp length cost of one dyadic detector block -/

namespace Ostmann

 theorem density_dyadic_power_cost (m Y Q T σ : ℝ) (hm : 0 < m) (hmY : m ≤ Y)
    (hT : 1 ≤ T) (_hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ((2 * m + Q ^ 2 * (T + 1)) * (2 * m)) / m ^ (2 * σ) ≤
      4 * (Y ^ (2 - 2 * σ) + (Q ^ 2 * T) * m ^ (1 - 2 * σ)) := by
  have hq : Q ^ 2 * (T + 1) ≤ 2 * (Q ^ 2 * T) := by nlinarith [sq_nonneg Q]
  have hfirst := Real.rpow_le_rpow hm.le hmY (by linarith : 0 ≤ 2 - 2 * σ)
  have hpower2 : m ^ (2 - 2 * σ) = m ^ 2 / m ^ (2 * σ) := by
    rw [Real.rpow_sub hm, Real.rpow_two]
  have hpower1 : m ^ (1 - 2 * σ) = m / m ^ (2 * σ) := by
    rw [Real.rpow_sub hm, Real.rpow_one]
  calc
    _ ≤ (4 * (m + Q ^ 2 * T) * m) / m ^ (2 * σ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ = 4 * (m ^ (2 - 2 * σ) + (Q ^ 2 * T) * m ^ (1 - 2 * σ)) := by
      rw [hpower2, hpower1]
      ring
    _ ≤ _ := by gcongr

 theorem density_dyadic_log_cost (m Y : ℝ) (hm : 1 ≤ m) (hmY : m ≤ Y) :
    (2 + 64 * (Real.log (2 * m + 1)) ^ 2) * (2 + (Real.log (2 * m + 1)) ^ 2) *
      (1 + Real.log (2 * m)) ^ 3 ≤ 198 * (1 + Real.log (2 * Y + 1)) ^ 7 := by
  let L := 1 + Real.log (2 * Y + 1)
  have hY : 1 ≤ Y := hm.trans hmY
  have hlog : 0 ≤ Real.log (2 * Y + 1) := Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have h1 : 0 ≤ Real.log (2 * m + 1) := Real.log_nonneg (by linarith)
  have h1L : Real.log (2 * m + 1) ≤ L := by
    have h := Real.log_le_log (by linarith : 0 < 2 * m + 1) (by linarith : 2 * m + 1 ≤ 2 * Y + 1)
    dsimp [L]
    linarith
  have hs : (Real.log (2 * m + 1)) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h1 h1L 2
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have ha : 2 + 64 * (Real.log (2 * m + 1)) ^ 2 ≤ 66 * L ^ 2 := by nlinarith
  have hb : 2 + (Real.log (2 * m + 1)) ^ 2 ≤ 3 * L ^ 2 := by nlinarith
  have hc0 : 0 ≤ 1 + Real.log (2 * m) := by
    have h := Real.log_nonneg (by linarith : 1 ≤ 2 * m)
    linarith
  have hc : 1 + Real.log (2 * m) ≤ L := by
    dsimp [L]
    have h : Real.log (2 * m) ≤ Real.log (2 * Y + 1) :=
      Real.log_le_log (by linarith : 0 < 2 * m) (by linarith : 2 * m ≤ 2 * Y + 1)
    exact add_le_add le_rfl h
  calc
    _ ≤ (66 * L ^ 2) * (3 * L ^ 2) * L ^ 3 := by
      exact mul_le_mul (mul_le_mul ha hb (by positivity) (by positivity))
        (pow_le_pow_left₀ hc0 hc 3) (by positivity) (by positivity)
    _ = _ := by dsimp [L]; ring

 theorem density_dyadic_total_cost (C x m Y Q T σ : ℝ) (hC : 0 ≤ C)
    (hx : 1 ≤ x) (hxm : x ≤ m) (hmY : m ≤ Y) (hT : 1 ≤ T)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    C * (2 * m + Q ^ 2 * (T + 1)) *
      (2 + 64 * (Real.log (2 * m + 1)) ^ 2) * (2 + (Real.log (2 * m + 1)) ^ 2) *
      (2 * m * (1 + Real.log (2 * m)) ^ 3 / m ^ (2 * σ)) ≤
    (792 * C) * (1 + Real.log (2 * Y + 1)) ^ 7 *
      (Y ^ (2 - 2 * σ) + Q ^ 2 * T * x ^ (1 - 2 * σ)) := by
  have hm : 0 < m := by linarith
  have hlogY : 0 ≤ Real.log (2 * Y + 1) := Real.log_nonneg (by linarith)
  have hl := density_dyadic_log_cost m Y (hx.trans hxm) hmY
  have hp := density_dyadic_power_cost m Y Q T σ hm hmY hT hσ hσ1
  have hr := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x) hxm (by linarith : 1 - 2 * σ ≤ 0)
  have hp' : ((2 * m + Q ^ 2 * (T + 1)) * (2 * m)) / m ^ (2 * σ) ≤
      4 * (Y ^ (2 - 2 * σ) + Q ^ 2 * T * x ^ (1 - 2 * σ)) := by
    apply hp.trans
    gcongr
  calc
    _ = C * ((2 + 64 * (Real.log (2 * m + 1)) ^ 2) * (2 + (Real.log (2 * m + 1)) ^ 2) *
      (1 + Real.log (2 * m)) ^ 3) * (((2 * m + Q ^ 2 * (T + 1)) * (2 * m)) / m ^ (2 * σ)) := by ring
    _ ≤ C * (198 * (1 + Real.log (2 * Y + 1)) ^ 7) *
        (4 * (Y ^ (2 - 2 * σ) + Q ^ 2 * T * x ^ (1 - 2 * σ))) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hl hC) hp' (by positivity) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI
