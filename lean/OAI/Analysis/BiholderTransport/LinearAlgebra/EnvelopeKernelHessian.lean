import Mathlib
import OAI.Analysis.BiholderTransport.Contact.EnvelopePole

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma envelope_kernel_second_derivative {C : E×E → ℝ} {f : E → ℝ}
    {a : E → E} {p : E} {R : E →L[ℝ] E}
    (hC : ContDiffAt ℝ 2 C (a p,p))
    (ha : HasFDerivAt a R p)
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q)
    (hsupport : ∀ᶠ q in 𝓝 p, ∀ᶠ v in 𝓝 q,
      f v≤f q+C (a q,v)-C (a q,q)) :
    ∀ d e:E, fderiv ℝ (fderiv ℝ f) p d e=
      fderiv ℝ (fderiv ℝ C) (a p,p) (R d,d) (0,e) := by
  let I : E →L[ℝ] E×E := (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)
  let G : E → E →L[ℝ] ℝ := fun q => (fderiv ℝ C (a q,q)).comp I
  have hmap := ha.prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := ((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun q => (a q,q)) p hmap
  have hG := hd.clm_comp (hasFDerivAt_const I p)
  have heq : fderiv ℝ f =ᶠ[𝓝 p] G := by
    have hn := hmap.continuousAt.eventually (hC.eventually (by norm_num))
    filter_upwards [hf,hsupport,hn] with q hq hs hreg
    let g : E → ℝ := fun v => f q+C (a q,v)-C (a q,q)
    have hD := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun v : E => (a q,v)) q
      ((hasFDerivAt_const (a q) q).prodMk (hasFDerivAt_id q))
    have hg : HasFDerivAt g (G q) q := by
      convert! (hD.const_add (f q)).sub_const (C (a q,q)) using 1
    rw [upper_contact_fderiv hq hg.differentiableAt hs (by dsimp [g]; ring)]
    exact hg.fderiv
  intro d e
  have H := congrArg (fun J : E →L[ℝ] E →L[ℝ] ℝ => J d e)
    (hG.congr_of_eventuallyEq heq).fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,map_zero,ContinuousLinearMap.comp_zero,
    add_zero,zero_add,add_apply,zero_apply,I] using H

lemma envelope_selector_injective_of_hessian_gap {C : E×E → ℝ} {f : E → ℝ}
    {a : E → E} {p : E} {R : E →L[ℝ] E}
    (hC : ContDiffAt ℝ 2 C (a p,p)) (ha : HasFDerivAt a R p)
    (hf : ∀ᶠ q in 𝓝 p,DifferentiableAt ℝ f q)
    (hsupport : ∀ᶠ q in 𝓝 p, ∀ᶠ v in 𝓝 q,
      f v≤f q+C (a q,v)-C (a q,q))
    {b k : ℝ} (hbk : b < k)
    (hupper : ∀ d:E,fderiv ℝ (fderiv ℝ f) p d d≤b*‖d‖^2)
    (hlower : ∀ d:E,k*‖d‖^2≤fderiv ℝ (fderiv ℝ C) (a p,p) (0,d) (0,d)) :
    Function.Injective R := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro d hd
  change R d = 0 at hd
  have H := envelope_kernel_second_derivative hC ha hf hsupport d d
  rw [hd] at H
  have hu := hupper d
  have hl := hlower d
  rw [H] at hu
  have hz : ‖d‖^2=0 := by nlinarith only [hu,hl,hbk,sq_nonneg ‖d‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end WeakMTWTransport

end

end OAI
