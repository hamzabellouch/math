import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBudgetSize
import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterHeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_commonCenter_multiplier_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      (quadraticLiftMultiplierBound Z : ℝ) ≤ (parameterX T : ℝ)^ε := by
  filter_upwards [eventually_parameterX_log_bounds,
    eventually_mul_rpow_le_rpow (52/ε) (a := 1) (b := 8/5) (by norm_num),
    eventually_ge_atTop (4 : ℝ)] with T hX hg hT4
  intro Z hZl hZu
  have hlogZ : 0 < Real.log Z := by linarith
  have hZp : (0 : ℝ) < Z :=
    lt_trans (by norm_num) ((Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ)
  have hZ2 : (2 : ℝ) ≤ Z := by
    have h := Real.log_le_self hZp.le
    linarith
  have hZ1 : 1 ≤ Z := by exact_mod_cast (show (1 : ℝ) ≤ Z by linarith)
  have hXp : (0 : ℝ) < parameterX T :=
    lt_trans (by norm_num) ((Real.log_pos_iff (Nat.cast_nonneg (parameterX T))).mp
      (show 0 < Real.log (parameterX T : ℝ) by linarith [hX.2.1]))
  rw [Real.rpow_one] at hg
  have hg' := mul_le_mul_of_nonneg_right hg hε.le
  have he : (52/ε)*T*ε = 52*T := by field_simp
  rw [he] at hg'
  have hx := mul_le_mul_of_nonneg_left hX.2.2.1 hε.le
  have hlog : 2*Real.log Z ≤ ε*Real.log (parameterX T : ℝ) := by nlinarith
  have hcap := quadraticLiftMultiplierBound_le Z hZ1
  have hp := Real.rpow_le_self_of_one_le
    (show (1 : ℝ) ≤ Z by linarith) (by norm_num : (13/100 : ℝ) ≤ 1)
  calc
    (quadraticLiftMultiplierBound Z : ℝ) ≤ (Z : ℝ)^2 := by nlinarith
    _ = Real.exp (2*Real.log Z) := by
      rw [show (2 : ℝ)*Real.log Z = (2 : ℕ)*Real.log (Z : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hZp]
    _ ≤ Real.exp (ε*Real.log (parameterX T : ℝ)) := Real.exp_le_exp.mpr hlog
    _ = (parameterX T : ℝ)^ε := by
      rw [Real.rpow_def_of_pos hXp]
      congr 1
      ring

end Ostmann.QuadraticCenter

end

end OAI
