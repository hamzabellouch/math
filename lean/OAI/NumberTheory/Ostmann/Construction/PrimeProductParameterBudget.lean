import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # Numerical overhead in the fixed-family prime-product moment estimate -/

namespace Ostmann

open Filter Asymptotics

/-- The transfer-factor logarithm is negligible after division by the
moment order. The small positive gap `mu + kappa - 1` is used explicitly. -/
theorem eventual_prime_product_parameter_budget (C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ k l : ℝ,
      0 ≤ k → k ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (1 / 1000000 : ℝ) / 2 ≤ l → l ≤ T ^ (1 / 1000000 : ℝ) →
      C * T + k * (C + 3 * Real.log T) + C * l ≤
        ε * l * T ^ (9999999 / 10000000 : ℝ) := by
  let μ : ℝ := 1 / 1000000
  let κ : ℝ := 9999999 / 10000000
  let A := 4 * C + 6
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 2 / 5 by norm_num)).bound zero_lt_one
  have hpower := (tendsto_rpow_atTop (show 0 < κ + μ - 1 by norm_num [κ, μ])).eventually_ge_atTop
    (2 * A / ε)
  filter_upwards [hlog, hpower, eventually_ge_atTop (1 : ℝ)] with T hl hp hT k l hk hkU hlL hlU
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl' : Real.log T ≤ T ^ (2 / 5 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogT,
      abs_of_nonneg (Real.rpow_nonneg hT0.le _), one_mul] using hl
  have hρ : T ^ (3 / 5 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (3 / 5 : ℝ) ≤ 1 by norm_num)
  have hμ : T ^ μ ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show μ ≤ 1 by norm_num [μ])
  have hklog : k * Real.log T ≤ 2 * T := by
    calc
      _ ≤ (2 * T ^ (3 / 5 : ℝ)) * T ^ (2 / 5 : ℝ) :=
        mul_le_mul hkU hl' hlogT (by positivity)
      _ = 2 * T := by
        rw [mul_assoc, ← Real.rpow_add hT0]
        norm_num
  have hrough : C * T + k * (C + 3 * Real.log T) + C * l ≤ A * T := by
    have hkT : k ≤ 2 * T := hkU.trans (mul_le_mul_of_nonneg_left hρ (by norm_num))
    have hlT : l ≤ T := hlU.trans hμ
    have hkC := mul_le_mul_of_nonneg_left hkT hC
    have hlC := mul_le_mul_of_nonneg_left hlT hC
    dsimp [A]
    nlinarith
  apply hrough.trans
  have hp' : A ≤ ε / 2 * T ^ (κ + μ - 1) := by
    have hh := (div_le_iff₀ hε).mp hp
    calc
      A = (2 * A) / 2 := by ring
      _ ≤ (T ^ (κ + μ - 1) * ε) / 2 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring
  have hcombined : T ^ (κ + μ - 1) * T = T ^ μ * T ^ κ := by
    calc
      _ = T ^ (κ + μ - 1) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ ((κ + μ - 1) + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (μ + κ) := by congr 1; ring
      _ = _ := Real.rpow_add hT0 _ _
  calc
    A * T ≤ (ε / 2 * T ^ (κ + μ - 1)) * T :=
      mul_le_mul_of_nonneg_right hp' hT0.le
    _ = ε * (T ^ μ / 2) * T ^ κ := by
      calc
        _ = ε / 2 * (T ^ (κ + μ - 1) * T) := by ring
        _ = _ := by rw [hcombined]; ring
    _ ≤ ε * l * T ^ κ := by gcongr

/-- The nonsquare character-sum error is exponentially small because
the number of sampled primes grows faster than the moment order. -/
theorem eventual_prime_product_error_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in atTop, ∀ k l : ℝ,
      T ^ (3 / 5 : ℝ) / 2 ≤ k →
      1 ≤ l → l ≤ T ^ (1 / 1000000 : ℝ) →
      C * T + C * l + 2 * C * l * T + k * (C + 3 * Real.log T - T) ≤
        -20 * l * T := by
  let μ : ℝ := 1 / 1000000
  let D := 4 * C + 20
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
    (show (0 : ℝ) < 1 / 12 by norm_num)
  have hpower := (tendsto_rpow_atTop (show (0 : ℝ) < 3 / 5 - μ by norm_num [μ])).eventually_ge_atTop
    (4 * D)
  filter_upwards [hlog, hpower, eventually_ge_atTop (4 * C),
    eventually_ge_atTop (1 : ℝ)] with T hl hp hCT hT k l hk hl1 hlU
  have hT0 : 0 < T := by linarith
  have hk0 : 0 ≤ k := le_trans (by positivity) hk
  have hl0 : 0 ≤ l := by linarith
  have hlog' : Real.log T ≤ T / 12 := by
    simpa only [Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hT), abs_of_nonneg hT0.le, one_div_mul_eq_div] using hl
  have hnegative : C + 3 * Real.log T - T ≤ -T / 2 := by linarith
  have hkl : D * l ≤ k / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hT0.le μ)
    have hpowers : T ^ (3 / 5 - μ) * T ^ μ = T ^ (3 / 5 : ℝ) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring
    rw [hpowers] at hmul
    have hDl := mul_le_mul_of_nonneg_left hlU hD
    nlinarith only [hmul, hDl, hk]
  have hCT' : C * T ≤ C * l * T :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hl1) hT0.le
  have hCl : C * l ≤ C * l * T := by
    exact le_mul_of_one_le_right (mul_nonneg hC hl0) hT
  have hkn := mul_le_mul_of_nonneg_left hnegative hk0
  have hklT := mul_le_mul_of_nonneg_right hkl hT0.le
  dsimp [D] at hklT
  nlinarith only [hCT', hCl, hkn, hklT]

end Ostmann

end OAI
