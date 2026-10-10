import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterAuxiliaryChoice

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

lemma auxiliaryK_mul_bounds {T y : ℝ} {Z z : ℕ} (hT : 0 ≤ T)
    (hy : 0 < y) (hy2 : Real.log 2 ≤ y)
    (hZl : T / 2 ≤ Real.log Z) (hZu : Real.log Z ≤ 2 * T)
    (hz : 1 ≤ z) (hzl : y / 2 ≤ Real.log z) (hzu : Real.log z ≤ 2 * y) :
    T ≤ 300 * y * ((auxiliaryK Z z : ℝ) + 1) ∧ (auxiliaryK Z z : ℝ) * y ≤ T := by
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hdenl : y / 2 ≤ Real.log (2 * (z : ℝ)) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hzr.ne']
    linarith
  have hdenu : Real.log (2 * (z : ℝ)) ≤ 3 * y := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hzr.ne']
    linarith
  have hden : 0 < Real.log (2 * (z : ℝ)) := by linarith
  have hnum : 0 ≤ (1 / 50 : ℝ) * Real.log Z := by nlinarith
  have hfloor : (1 / 50 : ℝ) * Real.log Z / Real.log (2 * (z : ℝ)) <
      (auxiliaryK Z z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hupper : (auxiliaryK Z z : ℝ) ≤
      (1 / 50 : ℝ) * Real.log Z / Real.log (2 * (z : ℝ)) := Nat.floor_le (div_nonneg hnum hden.le)
  have hl := (div_lt_iff₀ hden).mp hfloor
  have hu := (le_div_iff₀ hden).mp hupper
  have hk : (0 : ℝ) ≤ auxiliaryK Z z := Nat.cast_nonneg _
  constructor <;> nlinarith

theorem eventually_auxiliaryK_bounds :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent →
      T ^ (3 / 4 : ℝ) ≤ (auxiliaryK Z z : ℝ) ∧
      (auxiliaryK Z z : ℝ) ≤ T ^ (1 - auxiliaryExponent) := by
  filter_upwards [eventually_auxiliary_size_conditions,
    eventually_mul_rpow_le_rpow 600 (a := 3 / 4 + auxiliaryExponent) (b := 1)
      (by norm_num [auxiliaryExponent])] with T hc hg
  intro Z z hZl hZu hz hzl hzu
  have hT : 0 < T := by linarith [hc.1]
  have hy : 0 < T ^ auxiliaryExponent := Real.rpow_pos_of_pos hT _
  have hb := auxiliaryK_mul_bounds hT.le hy (by linarith [hc.2.2.1]) hZl hZu hz hzl hzu
  have hp : T ^ auxiliaryExponent * T ^ (3 / 4 : ℝ) = T ^ (3 / 4 + auxiliaryExponent) := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  have hp1 : 1 ≤ T ^ (3 / 4 : ℝ) := Real.one_le_rpow hc.1 (by norm_num)
  rw [Real.rpow_one, ← hp] at hg
  constructor
  · nlinarith [hb.1]
  · have hid : T ^ auxiliaryExponent * T ^ (1 - auxiliaryExponent) = T := by
      rw [← Real.rpow_add hT]
      convert Real.rpow_one T using 1; ring_nf
    nlinarith [hb.2]

end Ostmann.QuadraticCenter

end

end OAI
