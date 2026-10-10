import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions
import OAI.Analysis.BiholderTransport.CostGeometry.SplitStationary

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SplitEndpoint
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma diagonalSplitAction_endpoint_gradient {x : M}
    {p v : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    {r : TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hr : r∈injectivityDomain (riemannianExp x p))
    (heq : riemannianExp (riemannianExp x p) r=riemannianExp x (t • v))
    (hF : DifferentiableAt ℝ (diagonalSplitAction x t) (p,v))
    (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0)=
      -inner ℝ r (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
        (riemannianExp x) p k)/(1-t) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  have hc := cost_start_gradient_of_injectivityDomain hr
  rw [heq] at hc
  have hc' : HasMFDerivAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun z => cost (riemannianExp x (t • v)) z) y (innerSL ℝ (-r)) := by
    have hswap : (fun z => cost (riemannianExp x (t • v)) z)=
        (fun z => cost z (riemannianExp x (t • v))) := funext (fun z => cost_symm _ _)
    rw [hswap]
    exact hc
  have hE := (contMDiff_riemannianExp_fiber x p).mdifferentiableAt (by simp)
  have hD := hc'.comp p hE.hasMFDerivAt
  have hD' : HasFDerivAt (fun w : X => cost (riemannianExp x (t • v)) (riemannianExp x w))
      ((innerSL ℝ (-r)).comp (mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) p)) p := by
    convert! hD.hasFDerivAt using 1
  have hpart := (hD'.mul_const (1-t)⁻¹).const_add
    (cost x (riemannianExp x (t • v))/t)
  have heqfun : (fun w : X => diagonalSplitAction x t (w,v)) =
      (fun w : X => cost x (riemannianExp x (t • v))/t +
        cost (riemannianExp x (t • v)) (riemannianExp x w)*(1-t)⁻¹) := by
    funext w
    simp only [diagonalSplitAction,splitNormalAction,riemannianExp_zero,div_eq_mul_inv]
  rw [←heqfun] at hpart
  have hl := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const v p)
  have hfull := hF.hasFDerivAt.comp (f := fun w : X => (w,v)) p hl
  have H := congrArg (fun A : X →L[ℝ] ℝ => A k) (hfull.unique hpart)
  change fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0)=
    (1-t)⁻¹ * inner ℝ (-r) (mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) p k) at H
  rw [H,inner_neg_left,div_eq_mul_inv,mul_comm]

lemma diagonalSplitAction_mixed_endpoint {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hleft : t • p∈injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {q : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) (riemannianExp x p)}
    (hq : DifferentiableAt ℝ q p)
    (hqI : ∀ᶠ v in 𝓝 p, q v∈injectivityDomain (riemannianExp x p))
    (hqr : ∀ᶠ v in 𝓝 p, riemannianExp (riemannianExp x p) (q v)=riemannianExp x (t • v))
    (a k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,a) (k,0)=
      -inner ℝ (fderiv ℝ q p a) (mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n)
        (riemannianExp x) p k)/(1-t) := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let F := diagonalSplitAction (n := n) x t
  let E := mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp x) p
  have hF : ContDiffAt ℝ 2 F (p,p) := (diagonalSplitAction_contDiffAt hleft hright).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hl := (hasFDerivAt_const p p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hD := ((hdf.hasFDerivAt.comp (f := fun v : X => (p,v)) p hl).clm_apply
    (hasFDerivAt_const (k,(0:X)) p)).fderiv
  have hnF : ∀ᶠ v : X in 𝓝 p, DifferentiableAt ℝ F (p,v) :=
    (hl.continuousAt.eventually ((hF.of_le (m := 1) (by norm_num)).eventually (by norm_num))).mono
      (fun _ h => h.differentiableAt (by norm_num))
  have heq : (fun v : X => fderiv ℝ F (p,v) (k,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ (E k) (q v)*(1-t)⁻¹) := by
    filter_upwards [hnF,hqI,hqr] with v hv hvI hvr
    rw [diagonalSplitAction_endpoint_gradient hvI hvr hv,real_inner_comm,div_eq_mul_inv]
  have hi := (((innerSL ℝ (E k)).hasFDerivAt.comp p hq.hasFDerivAt).neg.mul_const (1-t)⁻¹).fderiv
  have H := congrArg (fun A : X →L[ℝ] ℝ => A a) (hD.symm.trans (heq.fderiv_eq.trans hi))
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,_root_.zero_apply,
    map_zero,zero_add,ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply,
    _root_.smul_apply,smul_eq_mul,_root_.neg_apply] at H
  change fderiv ℝ (fderiv ℝ F) (p,p) (0,a) (k,0)=
    (1-t)⁻¹ * (-inner ℝ (E k) (fderiv ℝ q p a)) at H
  rw [H,real_inner_comm,div_eq_mul_inv,mul_comm]

end SplitEndpoint
end WeakMTWTransport

end

end

end

end OAI
