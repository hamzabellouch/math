import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBudgetIntervals

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_kernelCoefficient_cutoff_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      (((2*Z)^evenMomentParameter (parameterX T) Z : ℕ) : ℝ) ≤
        (parameterX T : ℝ)^(1+ε) := by
  filter_upwards [eventually_kernelCoefficient_intervals, eventually_parameterX_log_bounds,
    eventually_mul_rpow_le_rpow (52/ε) (a := 1) (b := 8/5) (by norm_num)]
    with T hinter hX hg
  intro Z hZl hZu
  have hT : 0 < T := by linarith [hX.1]
  have hlogZ : 0 < Real.log Z := by linarith [hX.1]
  have hZp : (0 : ℝ) < Z :=
    lt_trans (by norm_num) ((Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ)
  have hXp : (0 : ℝ) < parameterX T :=
    lt_trans (by norm_num) ((Real.log_pos_iff (Nat.cast_nonneg (parameterX T))).mp
      (show 0 < Real.log (parameterX T : ℝ) by linarith [hX.2.1]))
  rw [Real.rpow_one] at hg
  have hg' := mul_le_mul_of_nonneg_right hg hε.le
  have he : (52/ε)*T*ε = 52*T := by field_simp
  rw [he] at hg'
  have hx := mul_le_mul_of_nonneg_left hX.2.2.1 hε.le
  have hlog : 13*Real.log Z ≤ ε*Real.log (parameterX T : ℝ) := by nlinarith
  have hz13 : (Z : ℝ)^13 ≤ (parameterX T : ℝ)^ε := by
    calc
      _ = Real.exp (13*Real.log Z) := by
        rw [show (13 : ℝ)*Real.log Z = (13 : ℕ)*Real.log (Z : ℝ) by norm_num,
          Real.exp_nat_mul, Real.exp_log hZp]
      _ ≤ _ := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [Real.rpow_def_of_pos hXp]; congr 1; ring
  have hs : (((2*Z)^evenMomentParameter (parameterX T) Z : ℕ) : ℝ) ≤
      (parameterX T : ℝ)*(Z : ℝ)^13 := by exact_mod_cast (hinter Z hZl).2
  calc
    _ ≤ (parameterX T : ℝ)*(Z : ℝ)^13 := hs
    _ ≤ (parameterX T : ℝ)*(parameterX T : ℝ)^ε := mul_le_mul_of_nonneg_left hz13 hXp.le
    _ = _ := by rw [Real.rpow_add hXp, Real.rpow_one]

end Ostmann.QuadraticCenter

end

end OAI
