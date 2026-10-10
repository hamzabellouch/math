import Mathlib
import OAI.Analysis.BiholderTransport.Contact.EnvelopePole

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma stationary_contact_hessian {B : E×E → ℝ} {f : E → ℝ}
    {b : E → E} {x q : E} {R : E →L[ℝ] E}
    (hB : ContDiffAt ℝ 2 B (x,q)) (hb : HasFDerivAt b R x) (hb0 : b x=q)
    (hf : ∀ᶠ a in 𝓝 x, DifferentiableAt ℝ f a)
    (hle : ∀ᶠ z in 𝓝 (x,q), f z.1 ≤ B z)
    (heq : ∀ᶠ a in 𝓝 x, f a=B (a,b a)) :
    HasFDerivAt (fderiv ℝ f)
      ((fderiv ℝ (fderiv ℝ B) (x,q)).comp
        ((ContinuousLinearMap.id ℝ E).prod R) |>.flip |>.comp
          ((ContinuousLinearMap.id ℝ E).prod 0) |>.flip) x := by
  let I : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod 0
  let L : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod R
  let G : E → E →L[ℝ] ℝ := fun a => (fderiv ℝ B (a,b a)).comp I
  have hmap := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk hb
  have hB' : ContDiffAt ℝ 2 B (x,b x) := by rwa [hb0]
  have hG := (((hB'.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a => (a,b a)) x hmap).clm_comp
      (hasFDerivAt_const I x)
  have he : fderiv ℝ f =ᶠ[𝓝 x] G := by
    have hn := hmap.continuousAt.eventually (hB'.eventually (by norm_num))
    have hln : ∀ᶠ a in 𝓝 x, ∀ᶠ z in 𝓝 (a,b a), f z.1 ≤ B z :=
      hmap.continuousAt.eventually (eventually_eventually_nhds.mpr (by simpa [hb0] using hle))
    filter_upwards [hf,heq,hn,hln] with a hfa hea hBa hla
    have ha : ContinuousAt (fun v : E => (v,b a)) a := by fun_prop
    have hlocal : ∀ᶠ v in 𝓝 a, f v ≤ B (v,b a) := ha.eventually hla
    have hd := (hBa.differentiableAt (by norm_num)).hasFDerivAt.comp
      (f := fun v : E => (v,b a)) a
      ((hasFDerivAt_id a).prodMk (hasFDerivAt_const (b a) a))
    exact (upper_contact_fderiv hfa hd.differentiableAt hlocal hea).trans hd.fderiv
  apply (hG.congr_of_eventuallyEq he).congr_fderiv
  ext d e
  simp only [hb0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_zero,
    zero_apply,zero_add,I]

lemma stationary_graph_middle_equation {B : E×E → ℝ}
    {b : E → E} {x q : E} {R : E →L[ℝ] E}
    (hB : ContDiffAt ℝ 2 B (x,q)) (hb : HasFDerivAt b R x) (hb0 : b x=q)
    (hstat : ∀ᶠ a in 𝓝 x, ∀ k : E, fderiv ℝ B (a,b a) (0,k)=0)
    (hmix : ∀ d k:E, fderiv ℝ (fderiv ℝ B) (x,q) (d,0) (0,k)= -inner ℝ d k)
    (d k:E) : fderiv ℝ (fderiv ℝ B) (x,q) (0,R d) (0,k)=inner ℝ d k := by
  have hB' : ContDiffAt ℝ 2 B (x,b x) := by rwa [hb0]
  have hd := (((hB'.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a => (a,b a)) x
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk hb)).clm_apply
        (hasFDerivAt_const ((0:E),k) x)
  have he : (fun a => fderiv ℝ B (a,b a) (0,k)) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have H := congrArg (fun A : E →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const (0:ℝ) x))
  simp only [hb0,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,map_zero,
    zero_apply,zero_add,add_apply] at H
  have hdR : (d,R d)=((d,0):E×E)+(0,R d) := by simp
  rw [hdR,map_add,add_apply,hmix] at H
  linarith

lemma diagonal_stationary_factorization {B : F×E → ℝ} {e : E → F}
    {p : E} {J : E →L[ℝ] F}
    (hB : ContDiffAt ℝ 2 B (e p,p)) (he : HasFDerivAt e J p)
    (hstat : ∀ᶠ v in 𝓝 p, ∀ k:E, fderiv ℝ B (e v,v) (0,k)=0)
    (d k:E) :
    fderiv ℝ (fderiv ℝ B) (e p,p) (0,d) (0,k)=
      -fderiv ℝ (fderiv ℝ B) (e p,p) (J d,0) (0,k) := by
  have hd := (((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v => (e v,v)) p
      (he.prodMk (hasFDerivAt_id (𝕜 := ℝ) p))).clm_apply
        (hasFDerivAt_const ((0:F),k) p)
  have hzero : (fun v => fderiv ℝ B (e v,v) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have H := congrArg (fun A : E →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq hzero.symm).unique (hasFDerivAt_const (0:ℝ) p))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,map_zero,
    zero_apply,zero_add,add_apply] at H
  have hdJ : (J d,d)=((J d,0):F×E)+(0,d) := by simp
  rw [hdJ,map_add,add_apply] at H
  linarith

end WeakMTWTransport

end

end OAI
