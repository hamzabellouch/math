import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterKBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

lemma isLittleO_rpow_of_lt {a b : ℝ} (hab : a < b) :
    (fun T : ℝ => T ^ a) =o[atTop] (fun T => T ^ b) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact fun h => (Real.rpow_pos_of_pos hT b).ne' h |>.elim
  · apply (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← Real.rpow_sub hT]
    congr 1
    ring

theorem eventually_evenMomentParameter_bound :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ, T / 2 ≤ Real.log Z →
      (evenMomentParameter (parameterX T) Z : ℝ) ≤ 14 * T ^ (3 / 5 : ℝ) := by
  filter_upwards [eventually_parameterX_log_bounds] with T hb
  intro Z hZ
  have hT : 0 < T := by linarith [hb.1]
  have hlogZ : 0 < Real.log Z := by linarith
  have hlogX : 0 ≤ Real.log (parameterX T : ℝ) := by linarith [hb.2.1]
  have hp : 0 < T ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hT _
  have hp1 : 1 ≤ T ^ (3 / 5 : ℝ) := Real.one_le_rpow hb.1 (by norm_num)
  have hid : T * T ^ (3 / 5 : ℝ) = T ^ (8 / 5 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hT]
    norm_num
  have hratio : Real.log (parameterX T : ℝ) / Real.log Z ≤ 2 * T ^ (3 / 5 : ℝ) := by
    apply (div_le_iff₀ hlogZ).mpr
    have hm := mul_le_mul_of_nonneg_right hZ hp.le
    nlinarith [hb.2.2.2.1]
  have he := evenMomentParameter_bounds (parameterX T) Z
    (show 0 ≤ Real.log (parameterX T : ℝ) / Real.log Z + 10 by positivity)
  linarith [he.2]

theorem eventually_moment_log_cost_le (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T / 2 ≤ Real.log Z → Real.log Z ≤ 2 * T →
      1 ≤ z → T ^ auxiliaryExponent / 2 ≤ Real.log z →
      Real.log z ≤ 2 * T ^ auxiliaryExponent →
      C * (evenMomentParameter (parameterX T) Z : ℝ) +
        C * Real.log (Real.log (parameterX T : ℝ)) ≤ ε * auxiliaryK Z z := by
  have hp := (isLittleO_rpow_of_lt (by norm_num : (3 / 5 : ℝ) < 3 / 4)).const_mul_left (14 * C)
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).const_mul_left (C * (8 / 5))
  have hsmall := (hp.add hl).bound hε
  filter_upwards [eventually_auxiliaryK_bounds, eventually_evenMomentParameter_bound,
    eventually_parameterX_log_bounds, hsmall] with T hK hk hX hs
  intro Z z hZl hZu hz hzl hzu
  have hT : 0 ≤ T := by linarith [hX.1]
  have hbound : 14 * C * T ^ (3 / 5 : ℝ) + C * (8 / 5) * Real.log T ≤
      ε * T ^ (3 / 4 : ℝ) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hT _)] at hs
    exact (le_abs_self _).trans hs
  have hk' := mul_le_mul_of_nonneg_left (hk Z hZl) hC.le
  have hl' := mul_le_mul_of_nonneg_left hX.2.2.2.2 hC.le
  have hK' := mul_le_mul_of_nonneg_left (hK Z z hZl hZu hz hzl hzu).1 hε.le
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
