import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.SplitStationary

namespace OAI

noncomputable section

namespace WeakMTWTransport

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma diagonal_stationary_hessian_null {F : E×E → ℝ} {p k : E}
    (hF : ContDiffAt ℝ 2 F (p,p))
    (hstat : ∀ᶠ v in 𝓝 p, fderiv ℝ F (v,v) (0,k)=0)
    (hker : ∀ᶠ v in 𝓝 p, fderiv ℝ F (p,v) (k,0)=0) :
    fderiv ℝ (fderiv ℝ F) (p,p) (0,k) (0,k)=0 := by
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let L : E →L[ℝ] E×E := (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)
  have hD₁ := ((hdf.hasFDerivAt.comp (f := fun v : E => (v,v)) p L.hasFDerivAt).clm_apply
    (hasFDerivAt_const ((0:E),k) p)).fderiv
  have hz₁ : fderiv ℝ (fun v : E => fderiv ℝ F (v,v) (0,k)) p=0 := by
    have heq : (fun v : E => fderiv ℝ F (v,v) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := hstat
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have hd₁ := congrArg (fun A : E →L[ℝ] ℝ => A k) (hD₁.symm.trans hz₁)
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply,L,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] at hd₁
  have hL₂ : HasFDerivAt (fun v : E => (p,v))
      ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) p :=
    (hasFDerivAt_const p p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hD₂ := ((hdf.hasFDerivAt.comp (f := fun v : E => (p,v)) p hL₂).clm_apply
    (hasFDerivAt_const (k,(0:E)) p)).fderiv
  have hz₂ : fderiv ℝ (fun v : E => fderiv ℝ F (p,v) (k,0)) p=0 := by
    have heq : (fun v : E => fderiv ℝ F (p,v) (k,0)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) := hker
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have hd₂ := congrArg (fun A : E →L[ℝ] ℝ => A k) (hD₂.symm.trans hz₂)
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] at hd₂
  rw [(hF.isSymmSndFDerivAt (by simp)).eq] at hd₂
  have heq : (k,k)=(k,0)+((0:E),k) := by ext <;> simp
  rw [heq,map_add,add_apply,hd₂,zero_add] at hd₁
  exact hd₁
end

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma second_leg_cost_smooth {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ}
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (t • p),riemannianExp x p) := by
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨(sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hright
  dsimp only at hc
  rw [shifted_exp_endpoint] at hc
  simpa only [riemannianExp_smul] using hc

lemma diagonalSplitAction_endpoint_kernel {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p,
      fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0)=0 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  have he := (contMDiff_riemannianExp_fiber (n := n) x).mdifferentiable (by simp)
  have hc := (second_leg_cost_smooth hright).of_le (m := 1) (by simp)
  have hcn : ∀ᶠ z : M×M in 𝓝 (riemannianExp x (t • p),y),
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) 1
        (fun q : M×M => cost q.1 q.2) z :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hc
  have hj : Continuous (fun v : V => (riemannianExp x (t • v),y)) :=
    ((continuous_riemannianExp x).comp (by fun_prop)).prodMk continuous_const
  have hcnear := hj.continuousAt.eventually hcn
  have hF := diagonalSplitAction_contDiffAt hleft hright
  have hFn := (hF.of_le (m := 1) (by simp)).eventually (by norm_num)
  have hL : Continuous (fun v : V => (p,v)) := continuous_const.prodMk continuous_id
  have hFnear := hL.continuousAt.eventually hFn
  filter_upwards [hcnear,hFnear] with v hcv hFv
  change ContDiffAt ℝ 1 (diagonalSplitAction x t) (p,v) at hFv
  have hcost := (hcv.comp y (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by norm_num)
  have hD := hcost.hasMFDerivAt.comp p (he p).hasMFDerivAt
  have hD' : HasFDerivAt (fun w : V => cost (riemannianExp x (t • v)) (riemannianExp x w))
      ((mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ) (fun z => cost (riemannianExp x (t • v)) z) y).comp
        (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp x) p)) p := by
    convert! hD.hasFDerivAt using 1
  have hpart := (hD'.mul_const (1-t)⁻¹).const_add
    (cost x (riemannianExp x (t • v))/t)
  have heqfun : (fun w : V => diagonalSplitAction x t (w,v)) =
      (fun w : V => cost x (riemannianExp x (t • v))/t +
        cost (riemannianExp x (t • v)) (riemannianExp x w)*(1-t)⁻¹) := by
    funext w
    simp only [diagonalSplitAction,splitNormalAction,riemannianExp_zero,div_eq_mul_inv]
  rw [←heqfun] at hpart
  have hl := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk (hasFDerivAt_const v p)
  have hfull := (hFv.differentiableAt (by norm_num)).hasFDerivAt.comp
    (f := fun w : V => (w,v)) p hl
  have hh := congrArg (fun A : V →L[ℝ] ℝ => A k) (hfull.unique hpart)
  change fderiv ℝ (diagonalSplitAction x t) (p,v) (k,0) =
    (1-t)⁻¹ • (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (fun z => cost (riemannianExp x (t • v)) z) y)
      (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,Model n) (riemannianExp x) p k) at hh
  rw [hk,map_zero,smul_zero] at hh
  exact hh

lemma diagonalSplitAction_conjugate_hessian_null {x : M} {p k : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0) :
    fderiv ℝ (fderiv ℝ (diagonalSplitAction x t)) (p,p) (0,k) (0,k)=0 := by
  apply diagonal_stationary_hessian_null
    ((diagonalSplitAction_contDiffAt hleft hright).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  · exact (split_regular_legs_near hleft hright).mono
      (fun v hv => diagonalSplitAction_stationary ht ht1 hv.1 hv.2 k)
  · exact diagonalSplitAction_endpoint_kernel hleft hright hk

end WeakMTWTransport

end

end OAI
