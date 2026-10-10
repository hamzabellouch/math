import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelectionSize

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Preliminaries Filter

lemma eventually_const_add_log_le_rpow (A B : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ T : ℝ in atTop, A + B * Real.log T ≤ T ^ r / 2 := by
  have hconst := (Asymptotics.isLittleO_const_id_atTop A).comp_tendsto (tendsto_rpow_atTop hr)
  have hlog := (isLittleO_log_rpow_atTop hr).const_mul_left B
  have hs := (hconst.add hlog).bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hs, eventually_ge_atTop (0 : ℝ)] with T h hT
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hT _)] at h
  exact (le_abs_self _).trans (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using h)

theorem eventually_auxiliary_size_conditions :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ T ∧ 1 ≤ T ^ auxiliaryExponent ∧
      2 * Real.log 2 ≤ T ^ auxiliaryExponent ∧
      Real.log 2 + 2 * (Real.log 4 + 4) +
          3 * collisionConstant 4 * Real.log (Real.log (parameterX T : ℝ)) ≤
        T ^ auxiliaryExponent / 2 ∧
      30 * T ^ 2 ≤ Real.exp (T ^ auxiliaryExponent / 2) := by
  have hc := eventually_const_add_log_le_rpow
    (Real.log 2 + 2 * (Real.log 4 + 4)) (3 * collisionConstant 4 * (8 / 5)) auxiliaryExponent_pos
  have he := eventually_const_add_log_le_rpow (Real.log 30) 2 auxiliaryExponent_pos
  filter_upwards [eventually_parameterX_log_bounds, hc, he,
    (tendsto_rpow_atTop auxiliaryExponent_pos).eventually_ge_atTop 1,
    (tendsto_rpow_atTop auxiliaryExponent_pos).eventually_ge_atTop (2 * Real.log 2)]
    with T hb hc he hy hy2
  have hT : 0 < T := by linarith [hb.1]
  refine ⟨hb.1, hy, hy2, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hb.2.2.2.2
      (show 0 ≤ 3 * collisionConstant 4 from mul_nonneg (by norm_num) (collisionConstant_pos 4).le)
    nlinarith
  · have h := Real.exp_le_exp.mpr he
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 30),
      show 2 * Real.log T = Real.log (T ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (sq_pos_of_pos hT)] at h
    exact h

end Ostmann.QuadraticCenter

end

end OAI
