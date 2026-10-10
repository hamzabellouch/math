import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.ZeroDensity.Scales

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.ZeroDensity

theorem eventually_sqrt_subpower_decay (K D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, 1 < X → Real.exp L ≤ Real.log X →
      Real.sqrt X*Real.exp (K*L*Real.exp (9*L/10)) ≤ X*Real.exp (-D*L) := by
  have hh := eventually_linear_mul_exp_le (a := (9 : ℝ)/10) (b := 1)
    (by norm_num) (2*(K+|D|))
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with L hh hL
  intro X hX hMX
  have hXp : 0 < X := by linarith
  have he : 1 ≤ Real.exp (9*L/10) := Real.one_le_exp (by positivity)
  have hDL : D*L ≤ |D| *L*Real.exp (9*L/10) := by
    calc
      D*L ≤ |D| *L := mul_le_mul_of_nonneg_right (le_abs_self D) (by linarith)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left he (show 0 ≤ |D| *L by positivity)
  have heq : (9 : ℝ)/10*L = 9*L/10 := by ring
  rw [heq,one_mul] at hh
  have hexponent : Real.log X/2+K*L*Real.exp (9*L/10) ≤ Real.log X-D*L := by
    nlinarith
  calc
    Real.sqrt X*Real.exp (K*L*Real.exp (9*L/10)) =
        Real.exp (Real.log X/2+K*L*Real.exp (9*L/10)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hXp, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.log X-D*L) := Real.exp_le_exp.mpr hexponent
    _ = X*Real.exp (-D*L) := by
      rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hXp]
      congr 2
      ring

theorem eventually_constant_exp_decay {C : ℝ} (hC : 0 < C) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, C*Real.exp (-(D+1)*L) ≤ Real.exp (-D*L) := by
  filter_upwards [eventually_ge_atTop (Real.log C)] with L hL
  have hCe : C ≤ Real.exp L := by
    calc
      C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ ≤ _ := Real.exp_le_exp.mpr hL
  calc
    _ ≤ Real.exp L*Real.exp (-(D+1)*L) :=
      mul_le_mul_of_nonneg_right hCe (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann.ZeroDensity

end

end OAI
