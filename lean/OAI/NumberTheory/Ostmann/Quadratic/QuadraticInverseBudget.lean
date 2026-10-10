import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveQuadraticInverse

namespace OAI

/-! # The explicit inverse losses are subexponential at the chosen K scale -/

namespace Ostmann

open Filter Asymptotics

theorem eventual_kernel_scale_sublinear (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ,
      K ≤ T ^ (9999999 / 10000000 : ℝ) → K ≤ ε * T := by
  have hp := (tendsto_rpow_atTop (show (0 : ℝ) < 1 - 9999999 / 10000000 by norm_num)).eventually_ge_atTop
    (1 / ε)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpow hT K hK
  have hTpos : 0 < T := by linarith
  have hh := mul_le_mul_of_nonneg_right hpow
    (Real.rpow_nonneg hTpos.le (9999999 / 10000000 : ℝ))
  rw [← Real.rpow_add hTpos,
    show (1 - 9999999 / 10000000 : ℝ) + 9999999 / 10000000 = 1 by norm_num,
    Real.rpow_one] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hε.le
  have he : ε * (1 / ε * T ^ (9999999 / 10000000 : ℝ)) =
      T ^ (9999999 / 10000000 : ℝ) := by field_simp
  rw [he] at hh'
  exact hK.trans hh'

theorem eventual_quadratic_inverse_cost (A m ε : ℝ) (hA : 0 ≤ A)
    (hm : 0 ≤ m) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ K : ℝ,
      K ≤ T ^ (9999999 / 10000000 : ℝ) →
      A * (1 + T) * Real.exp (m * K) ≤ Real.exp (ε * T) := by
  have hc : 0 < ε / (2 * (m + 1)) := by positivity
  have hp₀ := ((isLittleO_pow_exp_pos_mul_atTop 0 (show 0 < ε / 2 by positivity)).const_mul_left A)
  have hp₁ := ((isLittleO_pow_exp_pos_mul_atTop 1 (show 0 < ε / 2 by positivity)).const_mul_left A)
  have hp := (hp₀.add hp₁).bound zero_lt_one
  filter_upwards [eventual_kernel_scale_sublinear _ hc, hp,
    eventually_ge_atTop (0 : ℝ)] with T hKbound hpoly hT K hK
  have hpoly' : A * (1 + T) ≤ Real.exp (ε / 2 * T) := by
    simp only [pow_zero, pow_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ A + A * T),
      abs_of_pos (Real.exp_pos _), one_mul] at hpoly
    nlinarith only [hpoly]
  have hmk : m * K ≤ ε / 2 * T := by
    have hh := mul_le_mul_of_nonneg_left (hKbound K hK) hm
    have hc' : m * (ε / (2 * (m + 1))) ≤ ε / 2 := by
      have hratio : m / (m + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      calc
        _ = (ε / 2) * (m / (m + 1)) := by field_simp
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := mul_one _
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hc' hT])
  calc
    _ ≤ Real.exp (ε / 2 * T) * Real.exp (ε / 2 * T) := by
      exact mul_le_mul hpoly' (Real.exp_le_exp.mpr hmk) (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventual_quadratic_inverse_factor (B J : ℝ) (hB : 3 ≤ B) (hJ : 1 ≤ J) :
    ∀ᶠ T : ℝ in atTop, ∀ K Y : ℝ,
      K ≤ T ^ (9999999 / 10000000 : ℝ) →
      Real.exp (4 * T) ≤ Y → Y ≤ Real.exp (7 * T) →
      1024 * J ^ 4 * (1 + 2 * Real.log ((B + 1) * Y)) * Real.exp (4 * K) ≤
        Real.exp (T / 100) := by
  let A := 1024 * J ^ 4 * (15 + 2 * Real.log (B + 1))
  have hlogB : 0 ≤ Real.log (B + 1) := Real.log_nonneg (by linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventual_quadratic_inverse_cost A 4 (1 / 100) hA (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with T hcost hT K Y hK hYlo hYhi
  have hYpos : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hlogY : Real.log Y ≤ 7 * T := (Real.log_le_iff_le_exp hYpos).mpr hYhi
  rw [Real.log_mul (by linarith : B + 1 ≠ 0) hYpos.ne']
  have hh : 1 + 2 * (Real.log (B + 1) + Real.log Y) ≤
      (15 + 2 * Real.log (B + 1)) * (1 + T) := by nlinarith
  calc
    _ ≤ (1024 * J ^ 4 * ((15 + 2 * Real.log (B + 1)) * (1 + T))) * Real.exp (4 * K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) (Real.exp_nonneg _)
    _ = A * (1 + T) * Real.exp (4 * K) := by dsimp [A]; ring
    _ ≤ _ := by simpa only [one_div_mul_eq_div] using hcost K hK

end Ostmann

end OAI
