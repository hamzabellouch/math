import OAI.Analysis.CircleDomains.Reflection.SmoothBeltramiDistortion

namespace OAI

/-! Exact antiholomorphic error of a smooth conjugated reflection. The
error is the failure of the smooth coefficient to obey reflection
invariance; no regularity of the limiting coefficient is assumed. -/
open Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma partials_conjugate {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    partialZ (fun w => star (f w)) z=star (partialBar f z) ∧
    partialBar (fun w => star (f w)) z=star (partialZ f z) := by
  have hd := ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => star (f w)) z=_ at hd
  simp only [partialZ,partialBar,hd,ContinuousLinearMap.comp_apply]
  change (star (fderiv ℝ f z 1)-Complex.I*star (fderiv ℝ f z Complex.I))/2=_ ∧
    (star (fderiv ℝ f z 1)+Complex.I*star (fderiv ℝ f z Complex.I))/2=_
  simp only [map_div₀,map_add,map_sub,map_mul,Complex.star_def,Complex.conj_I,map_ofNat]
  constructor <;> ring

lemma smooth_reflection_conjugate_error (F : ℂ ≃ₜ ℂ)
    (hF : Differentiable ℝ (F : ℂ → ℂ)) (hFi : Differentiable ℝ (F.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (he : ∀w,partialBar F w=μ w*partialZ F w)
    {R : ℂ → ℂ} {z : ℂ} (hR : DifferentiableAt ℝ R z) (hRz : partialZ R z=0) :
    partialBar (fun w => star (F (R (F.symm w)))) (F z)=
      star (partialZ F (R z)) *
        (partialBar R z*star (μ (R z))-μ z*star (partialBar R z)) *
        star (partialZ F.symm (F z)) := by
  have hn := smooth_homeomorph_partialZ_ne_zero F hF hFi μ he
  have hi := inverse_partialBar F hF hFi μ he hn (F z)
  have hFR := (hF (R z)).comp z hR
  have hH := (Complex.conjCLE.differentiableAt.comp z hFR)
  have hH' : DifferentiableAt ℝ (fun w => star (F (R w))) (F.symm (F z)) := by
    rw [F.symm_apply_apply]
    convert hH using 1; rfl
  have hc := (partials_comp hH' (hFi (F z))).2
  change partialBar ((fun w => star (F (R w))) ∘ F.symm) (F z)=_ at hc
  simp only [F.symm_apply_apply] at hi hc
  have hstar := partials_conjugate hFR
  have hcomp := partials_comp (hF (R z)) hR
  simp only [Function.comp_def] at hstar hcomp hc
  rw [hstar.1,hstar.2,hcomp.1,hcomp.2] at hc
  simp only [hRz,mul_zero,star_zero,zero_add,add_zero,he,hi] at hc
  rw [hc]
  simp only [star_mul,star_star]
  ring

lemma smooth_reflection_conjugate_phase_error (F : ℂ ≃ₜ ℂ)
    (hF : Differentiable ℝ (F : ℂ → ℂ)) (hFi : Differentiable ℝ (F.symm : ℂ → ℂ))
    (μ : ℂ → ℂ) (he : ∀w,partialBar F w=μ w*partialZ F w)
    {R : ℂ → ℂ} {z : ℂ} (hR : DifferentiableAt ℝ R z) (hRz : partialZ R z=0)
    (s : ℂ) (hs : partialBar R z=s*star (partialBar R z)) :
    partialBar (fun w => star (F (R (F.symm w)))) (F z)=
      star (partialZ F (R z))*star (partialBar R z)*
        (s*star (μ (R z))-μ z)*star (partialZ F.symm (F z)) := by
  rw [smooth_reflection_conjugate_error F hF hFi μ he hR hRz]
  conv_lhs => enter [1,2,1,1]; rw [hs]
  ring

end CircleDomainRigidity

end

end OAI
