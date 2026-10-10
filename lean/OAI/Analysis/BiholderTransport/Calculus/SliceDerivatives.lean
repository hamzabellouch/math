import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.SplitAction
import OAI.Analysis.BiholderTransport.Coordinates.BranchInverse
import OAI.Analysis.BiholderTransport.Calculus.JetPullback
import OAI.Analysis.BiholderTransport.Coordinates.FiberLog

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma fderiv_snd_slice {f : F×E → G} {a : F} {b : E}
    (hf : DifferentiableAt ℝ f (a,b)) (k : E) :
    fderiv ℝ (fun v : E => f (a,v)) b k=fderiv ℝ f (a,b) (0,k) := by
  have H := hf.hasFDerivAt.comp (f := fun v : E => (a,v)) b
    ((hasFDerivAt_const a b).prodMk (hasFDerivAt_id (𝕜 := ℝ) b))
  have HH := congrArg (fun L : E →L[ℝ] G => L k) H.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply] using HH

lemma second_fderiv_snd_slice {f : F×E → ℝ} {a : F} {b : E}
    (hf : ContDiffAt ℝ 2 f (a,b)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun t : E => f (a,t))) b v w=
      fderiv ℝ (fderiv ℝ f) (a,b) (0,v) (0,w) := by
  let I : E →L[ℝ] F×E := (0:E →L[ℝ] F).prod (ContinuousLinearMap.id ℝ E)
  have H := second_fderiv_comp_affine I (a,0) b (by simpa [I] using hf) v w
  simpa [I] using H

lemma second_fderiv_map_fst {B : F×G → ℝ} {e : E → F} {x : E} {y : G}
    (hB : ContDiffAt ℝ 2 B (e x,y)) (he : ContDiffAt ℝ 2 e x) (d : E) (k : G) :
    fderiv ℝ (fderiv ℝ (fun q : E×G => B (e q.1,q.2))) (x,y) (d,0) (0,k)=
      fderiv ℝ (fderiv ℝ B) (e x,y) (fderiv ℝ e x d,0) (0,k) := by
  let A := fun q : E×G => B (e q.1,q.2)
  have hA : ContDiffAt ℝ 2 A (x,y) :=
    hB.comp (x,y) ((he.comp (x,y) contDiffAt_fst).prodMk contDiffAt_snd)
  have hdA := (((hA.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a : E => (a,y)) x
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x))).clm_apply
        (hasFDerivAt_const ((0:E),k) x)
  have hdB := (((hB.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun a : E => (e a,y)) x
      ((he.differentiableAt (by norm_num)).hasFDerivAt.prodMk (hasFDerivAt_const y x))).clm_apply
        (hasFDerivAt_const ((0:F),k) x)
  have hnA : ∀ᶠ a in 𝓝 x, ContDiffAt ℝ 2 A (a,y) :=
    (continuousAt_id.prodMk continuousAt_const).eventually (hA.eventually (by norm_num))
  have hnB : ∀ᶠ a in 𝓝 x, ContDiffAt ℝ 2 B (e a,y) :=
    (he.continuousAt.prodMk continuousAt_const).eventually (hB.eventually (by norm_num))
  have heq : (fun a : E => fderiv ℝ A (a,y) (0,k)) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ B (e a,y) (0,k)) := by
    filter_upwards [hnA,hnB] with a ha hb
    rw [←fderiv_snd_slice (ha.differentiableAt (by norm_num)) k,
      ←fderiv_snd_slice (hb.differentiableAt (by norm_num)) k]
  have H := congrArg (fun L : E →L[ℝ] ℝ => L d)
    ((hdA.congr_of_eventuallyEq heq.symm).unique hdB)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply,map_zero,zero_apply,
    add_apply,add_zero,zero_add] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_joining_selector {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : p∈injectivityDomain x) (ht : 0 < t) (ht1 : t < 1) :
    ∃ b : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x,
      ContDiffAt ℝ ∞ b 0 ∧ b 0=p ∧
      (∀ᶠ a in 𝓝 0, normalCost x p a=splitNormalAction x t p (a,b a)) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
  let y := riemannianExp x p
  obtain ⟨P,hP,hP0,_,hPinv⟩ := exists_smooth_exp_branch z
    (riemannianExp_interior_nonconjugate hp)
  let Q : V → TangentBundle 𝓘(ℝ,Model n) M := fun a => P (riemannianExp x a,y)
  have hQ0 : Q 0=z := by dsimp [Q]; rw [riemannianExp_zero]; exact hP0
  have hmap : ContMDiffAt 𝓘(ℝ,V) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞
      (fun a : V => (riemannianExp x a,y)) 0 :=
    (contMDiff_riemannianExp_fiber x 0).prodMk contMDiffAt_const
  have hQ : ContMDiffAt 𝓘(ℝ,V) (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ Q 0 := by
    exact (show ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) ∞ P (riemannianExp x (0:V),y) from by
        simpa only [riemannianExp_zero] using hP).comp 0 hmap
  let Z : V → M := fun a => (sprayFlow t (Q a)).1
  have hZ : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,Model n) ∞ Z 0 :=
    (Bundle.contMDiff_proj (fun w : M => TangentSpace 𝓘(ℝ,Model n) w)).contMDiffAt.comp 0
      (contMDiff_sprayFlow.contMDiffAt.comp 0 (contMDiffAt_const.prodMk hQ))
  have hZ0 : Z 0=riemannianExp x (t • p) := by
    dsimp only [Z]; rw [hQ0]; exact (riemannianExp_smul x p t).symm
  have hpre := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  obtain ⟨L,hL,hL0,hLinv⟩ := exists_smooth_fiber_log hpre
  let b : V → V := fun a => t⁻¹ • L (Z a)
  have hb : ContDiffAt ℝ ∞ b 0 :=
    ((contDiffAt_const (c := t⁻¹)).smul ((show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L (Z 0) from
      hZ0 ▸ hL).comp 0 hZ).contDiffAt)
  have hb0 : b 0=p := by simp only [b,hZ0,hL0,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  refine ⟨b,hb,hb0,?_⟩
  have hQmin : ∀ᶠ a in 𝓝 (0:V), (Q a).2∈injectivityDomain (Q a).1 :=
    hQ.continuousAt.eventually (show {r : TangentBundle 𝓘(ℝ,Model n) M |
      r.2∈injectivityDomain r.1}∈𝓝 (Q 0) from by
        rw [hQ0]; exact isOpen_total_injectivityDomain.mem_nhds hp)
  have hQi : ∀ᶠ a in 𝓝 (0:V), (Q a).1=riemannianExp x a ∧
      riemannianExp (Q a).1 (Q a).2=y := by
    have H := hmap.continuousAt.eventually (show ∀ᶠ w in 𝓝 (riemannianExp x (0:V),y),
      (P w).1=w.1 ∧ riemannianExp (P w).1 (P w).2=w.2 from by
        simpa only [riemannianExp_zero] using hPinv)
    exact H
  have hZi : ∀ᶠ a in 𝓝 (0:V), riemannianExp x (t • b a)=Z a := by
    have H := hZ.continuousAt.eventually (show ∀ᶠ w in 𝓝 (Z 0), riemannianExp x (L w)=w from
      hZ0 ▸ hLinv)
    simpa only [b,smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using H
  filter_upwards [hQmin,hQi,hZi] with a ha hi hz
  have H := splitNormalAction_contact (injectivityDomain_subset_minimizingVectors _ ha) ht ht1
  simp only [splitNormalAction,normalCost,riemannianExp_zero] at H
  rw [riemannianExp_smul] at H
  change cost (Q a).1 (Z a)/t+cost (Z a) (riemannianExp (Q a).1 (Q a).2)/(1-t)=
    cost (Q a).1 (riemannianExp (Q a).1 (Q a).2) at H
  rw [hi.2,hi.1] at H
  change cost (riemannianExp x a) y =
    cost (riemannianExp x a) (riemannianExp x (t • b a))/t+
      cost (riemannianExp x (t • b a)) y/(1-t)
  rw [hz]
  exact H.symm

end WeakMTWTransport

end

end OAI
