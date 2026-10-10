import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma upper_contact_fderiv {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hle : f ≤ᶠ[𝓝 x] g) (heq : f x=g x) : fderiv ℝ f x=fderiv ℝ g x := by
  have hmin : IsLocalMin (g-f) x := by
    filter_upwards [hle] with y hy
    change g x-f x≤g y-f y
    rw [heq,sub_self]
    exact sub_nonneg.mpr hy
  have H := hmin.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hf.hasFDerivAt)
  exact (sub_eq_zero.mp H).symm

lemma envelope_pole_second_derivative {C : E×E → ℝ} {f : E → ℝ}
    {a : E → E} {p : E} {R : E →L[ℝ] E} {t : ℝ}
    (hC : ContDiffAt ℝ 2 C (0,p))
    (ha : HasFDerivAt a R p) (ha0 : a p=0)
    (hf : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ f q)
    (hsupport : ∀ᶠ q in 𝓝 p, ∀ᶠ v in 𝓝 q,
      f v≤f q+C (a q,v)-C (a q,q))
    (hqq : ∀ d e:E, fderiv ℝ (fderiv ℝ C) (0,p) (0,d) (0,e)=t*inner ℝ d e)
    (haq : ∀ d e:E, fderiv ℝ (fderiv ℝ C) (0,p) (d,0) (0,e) = -inner ℝ d e) :
    HasFDerivAt (fderiv ℝ f) (t • innerSL ℝ-(innerSL ℝ).comp R) p := by
  let I : E →L[ℝ] E×E := (0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)
  let G : E → E →L[ℝ] ℝ := fun q => (fderiv ℝ C (a q,q)).comp I
  have hmap := ha.prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hC' : ContDiffAt ℝ 2 C (a p,p) := by rwa [ha0]
  have hd := ((hC'.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := fun q => (a q,q)) p hmap
  have hG := hd.clm_comp (hasFDerivAt_const I p)
  have heq : fderiv ℝ f =ᶠ[𝓝 p] G := by
    have hn := hmap.continuousAt.eventually (hC'.eventually (by norm_num))
    filter_upwards [hf,hsupport,hn] with q hq hs hreg
    let g : E → ℝ := fun v => f q+C (a q,v)-C (a q,q)
    have hD := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun v : E => (a q,v)) q
      ((hasFDerivAt_const (a q) q).prodMk (hasFDerivAt_id q))
    have hg : HasFDerivAt g (G q) q := by
      convert! (hD.const_add (f q)).sub_const (C (a q,q)) using 1
    rw [upper_contact_fderiv hq hg.differentiableAt hs (by dsimp [g]; ring)]
    exact hg.fderiv
  apply (hG.congr_of_eventuallyEq heq).congr_fderiv
  ext d e
  simp only [ha0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_zero,
    zero_add,zero_apply,sub_apply,smul_apply,smul_eq_mul,
    innerSL_apply_apply,I]
  have he : (R d,d)=((R d,0):E×E)+(0,d) := by simp
  rw [he,map_add,add_apply,haq,hqq]
  change -inner ℝ (R d) e+t*inner ℝ d e = t*inner ℝ d e-inner ℝ (R d) e
  ring
end WeakMTWTransport

end

end OAI
