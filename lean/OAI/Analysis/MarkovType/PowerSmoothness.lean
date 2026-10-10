import OAI.Analysis.MarkovType.ScalarPowerRemainder
import OAI.Analysis.MarkovType.FiniteSmoothMoments
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def NormPowerSmoothWith (q C : ℝ) (X : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ x y : X, ‖x‖ = 1 → ‖y‖ = 1 → ∀ τ : ℝ, 0 ≤ τ →
    (‖x + τ • y‖ + ‖x - τ • y‖) / 2 ≤ 1 + C * τ ^ q

theorem norm_sum_le_of_powerSmooth {q C : ℝ}
    (hq : 1 < q) (h : NormPowerSmoothWith q C X)
    (x y : X) (hx : x ≠ 0) :
    ‖x + y‖ + ‖x - y‖ ≤
      2 * ‖x‖ + 2 * C * ‖y‖ ^ q * ‖x‖ ^ (1 - q) := by
  by_cases hy : y = 0
  · subst y
    simp [Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hq))] ; linarith
  let a : ℝ := ‖x‖
  let b : ℝ := ‖y‖
  have ha : 0 < a := norm_pos_iff.mpr hx
  have hb : 0 < b := norm_pos_iff.mpr hy
  have hax : ‖a⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    change a⁻¹ * a = 1
    exact inv_mul_cancel₀ ha.ne'
  have hby : ‖b⁻¹ • y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
    change b⁻¹ * b = 1
    exact inv_mul_cancel₀ hb.ne'
  have hcoeff : (b / a) * b⁻¹ = a⁻¹ := by
    field_simp [ha.ne', hb.ne']
  have hplus : a⁻¹ • x + (b / a) • (b⁻¹ • y) = a⁻¹ • (x + y) := by
    rw [smul_smul, hcoeff, smul_add]
  have hminus : a⁻¹ • x - (b / a) • (b⁻¹ • y) = a⁻¹ • (x - y) := by
    rw [smul_smul, hcoeff, smul_sub]
  have hunit := h (a⁻¹ • x) (b⁻¹ • y) hax hby (b / a) (div_nonneg hb.le ha.le)
  rw [hplus, hminus, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha)] at hunit
  have hscaled := mul_le_mul_of_nonneg_left hunit (show 0 ≤ 2 * a by positivity)
  have hleft :
      2 * a * ((a⁻¹ * ‖x + y‖ + a⁻¹ * ‖x - y‖) / 2) =
        ‖x + y‖ + ‖x - y‖ := by
    field_simp [ha.ne']
  rw [hleft] at hscaled
  have hpower : a * (b / a) ^ q = b ^ q * a ^ (1 - q) := by
    rw [Real.div_rpow hb.le ha.le, Real.rpow_sub ha, Real.rpow_one]
    ring
  change ‖x + y‖ + ‖x - y‖ ≤ 2 * a + 2 * C * b ^ q * a ^ (1 - q)
  calc
    ‖x + y‖ + ‖x - y‖ ≤ 2 * a * (1 + C * (b / a) ^ q) := hscaled
    _ = 2 * a + 2 * C * (a * (b / a) ^ q) := by ring
    _ = 2 * a + 2 * C * b ^ q * a ^ (1 - q) := by rw [hpower]; ring

theorem symmetricPowerSmoothWith_of_normPowerSmooth {q C : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hC : 0 ≤ C)
    (h : NormPowerSmoothWith q C X) :
    SymmetricPowerSmoothWith q (1 + q * C) X := by
  intro x y
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hD : 1 ≤ 1 + q * C := by
    have := mul_nonneg hq0.le hC
    linarith
  by_cases hx : x = 0
  · subst x
    simp only [zero_add, zero_sub, norm_neg, norm_zero, Real.zero_rpow hq0.ne',
      mul_zero, zero_add]
    have hn : 0 ≤ ‖y‖ ^ q := Real.rpow_nonneg (norm_nonneg y) q
    nlinarith
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hplus : |‖x + y‖ - ‖x‖| ≤ ‖y‖ := by
    simpa only [add_sub_cancel_left] using abs_norm_sub_norm_le (x + y) x
  have hminus : |‖x - y‖ - ‖x‖| ≤ ‖y‖ := by
    have hsub : (x - y) - x = -y := by abel
    simpa only [hsub, norm_neg] using abs_norm_sub_norm_le (x - y) x
  exact symmetric_rpow_le_of_sum_bound hq hq₂ hC ha (norm_nonneg y)
    (norm_nonneg (x + y)) (norm_nonneg (x - y)) hplus hminus
    (norm_sum_le_of_powerSmooth hq h x y hx)

end MarkovSuperreflexivity

end OAI
