import OAI.Analysis.CircleDomains.Sobolev.SmoothCutoffLinePayment

namespace OAI

/-! Unit affine lines in a real normed space pay through the actual
Fréchet derivative. This includes both coordinate directions in a rectangle. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem normed_affine_line_increment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ z, ‖fderiv ℝ f z‖ ≤ g z) (z e : E) (he : ‖e‖ ≤ 1) {x y : ℝ}
    (hgi : IntervalIntegrable (fun t => g (z+t • e)) volume x y) :
    |f (z+x • e)-f (z+y • e)| ≤ ∫ t in uIoc x y, g (z+t • e) := by
  apply smooth_line_increment_payment (hf.comp (by fun_prop)) hgi
  intro t _
  have hline : HasDerivAt (fun s : ℝ => z+s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add z
  have hder := ((hf.differentiable_one (z+t • e)).hasFDerivAt.comp_hasDerivAt t hline).deriv
  rw [hder,← Real.norm_eq_abs]
  exact ((fderiv ℝ f (z+t • e)).unit_le_opNorm e he).trans (hg _)

 theorem smooth_horizontal_increment {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (y x₁ x₂ : ℝ) : |f (x₁,y)-f (x₂,y)| ≤
      ∫ t in uIoc x₁ x₂, ‖fderiv ℝ f (t,y)‖ := by
  have hc : Continuous (fun t : ℝ => ‖fderiv ℝ f (t,y)‖) :=
    hf.continuous_fderiv (by norm_num) |>.norm |>.comp (by fun_prop)
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero] using
    normed_affine_line_increment hf (fun _ => le_rfl) (0,y) (1,0) (by simp)
      (by simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero]
        using hc.intervalIntegrable x₁ x₂)

 theorem smooth_vertical_increment {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (x y₁ y₂ : ℝ) : |f (x,y₁)-f (x,y₂)| ≤
      ∫ t in uIoc y₁ y₂, ‖fderiv ℝ f (x,t)‖ := by
  have hc : Continuous (fun t : ℝ => ‖fderiv ℝ f (x,t)‖) :=
    hf.continuous_fderiv (by norm_num) |>.norm |>.comp (by fun_prop)
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero] using
    normed_affine_line_increment hf (fun _ => le_rfl) (x,0) (0,1) (by simp)
      (by simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,mul_one,mul_zero,zero_add,add_zero]
        using hc.intervalIntegrable y₁ y₂)

end CircleDomainRigidity

end

end OAI
