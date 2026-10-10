import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBudgetAlgebra
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterSelection

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem kernelCoefficient_budget_base_le {J Z T c δ : ℝ} {k : ℕ}
    (hJ : 0 < J) (_hZ : 0 < Z) (hT : 1 ≤ T) (hc : 0 < c) (hδ : 0 < δ)
    (hlog : 0 < Real.log Z) (hcount : c*Z/Real.log Z ≤ J)
    (hZu : Real.log Z ≤ 2*T) (hk : (k : ℝ) ≤ T)
    (hTc : 4/(c*δ^2) ≤ T) :
    2*Z*(k : ℝ)/(J*δ^2) ≤ T^3 := by
  have hm := (div_le_iff₀ hlog).mp hcount
  have hratio : 2*Z*(k : ℝ)/(J*δ^2) ≤ 2*(k : ℝ)*Real.log Z/(c*δ^2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < J*δ^2) (by positivity : 0 < c*δ^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*(k : ℝ)*δ^2 by positivity)
    nlinarith
  have hklog : (k : ℝ)*Real.log Z ≤ 2*T^2 := by
    have hh := mul_le_mul hk hZu hlog.le (by linarith : 0 ≤ T)
    nlinarith
  calc
    _ ≤ 2*(k : ℝ)*Real.log Z/(c*δ^2) := hratio
    _ ≤ (4/(c*δ^2))*T^2 := by
      apply (div_le_iff₀ (by positivity : 0 < c*δ^2)).mpr
      have he : (4/(c*δ^2))*T^2*(c*δ^2) = 4*T^2 := by field_simp
      rw [he]
      nlinarith
    _ ≤ T*T^2 := mul_le_mul_of_nonneg_right hTc (sq_nonneg T)
    _ = _ := by ring

theorem eventually_kernelCoefficient_log_cost (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      Real.log 64+4*T+3*T*Real.log T ≤ ε*Real.log (parameterX T : ℝ) := by
  have hsmall := ((isLittleO_rpow_of_lt (by norm_num : (1 : ℝ) < 8/5)).const_mul_left 5).add
    (isLittleO_rpow_of_lt (by norm_num : (6/5 : ℝ) < 8/5))
  filter_upwards [hsmall.bound (by positivity : 0 < ε/2),
    eventually_const_add_log_le_rpow 0 3 (by norm_num : (0 : ℝ) < 1/5),
    eventually_parameterX_log_bounds, eventually_ge_atTop (Real.log 64)]
    with T hsmall hlog hX hTlog
  have hT : 0 < T := by linarith [hX.1]
  have hpow : T*T^(1/5 : ℝ) = T^(6/5 : ℝ) := by
    conv_lhs => lhs; rw [←Real.rpow_one T]
    rw [←Real.rpow_add hT]
    norm_num
  have hlogcost : 3*T*Real.log T ≤ T^(6/5 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog hT.le
    have hp : 0 ≤ T^(6/5 : ℝ) := Real.rpow_nonneg hT.le _
    simp only [zero_add] at hh
    rw [←mul_div_assoc, hpow] at hh
    nlinarith
  have hbound : 5*T+T^(6/5 : ℝ) ≤ (ε/2)*T^(8/5 : ℝ) := by
    simp only [Real.norm_eq_abs, Real.rpow_one,
      abs_of_nonneg (Real.rpow_nonneg hT.le (8/5 : ℝ))] at hsmall
    exact (le_abs_self _).trans hsmall
  have hx := mul_le_mul_of_nonneg_left hX.2.2.1 hε.le
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
