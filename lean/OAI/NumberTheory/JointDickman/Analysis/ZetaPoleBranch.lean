import OAI.NumberTheory.JointDickman.Analysis.ZetaPoleFactor
import OAI.NumberTheory.JointDickman.Analysis.AnalyticLogBranch

namespace OAI

/-! # A normalized analytic power of the pole-removed zeta function -/
namespace JointDickman
open Set

theorem zetaPoleFactor_differentiable : Differentiable ℂ zetaPoleFactor := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact zetaPoleFactor_analyticAt_one.differentiableAt
  · exact zetaPoleFactor_differentiableAt hs

theorem exists_zetaPoleLog {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (h1 : (1:ℂ) ∈ U) (hζ : ∀ s ∈ U, s ≠ 1 → riemannZeta s ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ f 1 = 0 ∧
      ∀ s ∈ U, Complex.exp (f s) = zetaPoleFactor s := by
  apply exists_normalized_analytic_log_on hUc hUo h1
    (fun s _ => zetaPoleFactor_differentiable.analyticAt s) _ zetaPoleFactor_one
  intro s hs
  by_cases he : s = 1
  · subst s
    simp only [zetaPoleFactor_one,ne_eq,one_ne_zero,not_false_eq_true]
  · rw [zetaPoleFactor_eq he]
    exact mul_ne_zero (sub_ne_zero.mpr he) (hζ s hs he)

theorem norm_exp_real_mul_of_exp_eq (z : ℝ) {w v : ℂ} (he : Complex.exp w = v) :
    ‖Complex.exp ((z:ℂ)*w)‖ = ‖v‖^z := by
  rw [←he,Complex.norm_exp,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,←Real.exp_mul]
  congr 1
  ring

end JointDickman

end OAI
