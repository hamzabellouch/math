import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeTaylor
import OAI.Analysis.BiholderTransport.Contact.SmoothSupportSemibound

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_comp_at {f : F → ℝ} {g : E → F} {x : E}
    (hnear : ∀ᶠ y in 𝓝 (g x),DifferentiableAt ℝ f y)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (g x))
    (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)+
        fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := hf.hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually hnear,hg.eventually (by norm_num)]
      with a hfa hga
    exact (hfa.hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,add_apply,add_comm] using H

lemma second_fderiv_comp_minorant_le {f q : F → ℝ} {g : E → F} {x : E}
    (hnear : ∀ᶠ y in 𝓝 (g x),DifferentiableAt ℝ f y)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (g x))
    (hq : ContDiffAt ℝ 2 q (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hval : q (g x)=f (g x)) (hlo : q≤ᶠ[𝓝 (g x)] f) (d:E) :
    fderiv ℝ (fderiv ℝ (fun a => q (g a))) x d d≤
      fderiv ℝ (fderiv ℝ (fun a => f (g a))) x d d := by
  have hd := (hnear.self_of_nhds).hasFDerivAt
  have hmin : IsLocalMin (fun y => f y-q y) (g x) := by
    filter_upwards [hlo] with y hy
    change f (g x)-q (g x)≤f y-q y
    rw [hval,sub_self]
    linarith only [hy]
  have hD : fderiv ℝ f (g x)=fderiv ℝ q (g x) :=
    sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero
      (hd.sub (hq.differentiableAt (by norm_num)).hasFDerivAt))
  have hj := hasSecondTaylor_of_second_derivative
    (hnear.mono (fun y hy => hy.hasFDerivAt)) hf.hasFDerivAt
  have H := hj.smooth_support_diag_le_at hd hq hval hlo (fderiv ℝ g x d)
  rw [second_fderiv_comp_with_acceleration hq hg,
    second_fderiv_comp_at hnear hf hg,hD]
  linarith only [H]

end WeakMTWTransport

end

end OAI
