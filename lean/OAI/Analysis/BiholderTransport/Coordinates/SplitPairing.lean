import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.SplitAction

namespace OAI

noncomputable section

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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma normalCost_fderiv_zero {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (normalCost x p) 0 xi = -inner ℝ p xi := by
  have H := (normalCost_radial_fderiv_near_zero hp xi).self_of_nhds
  simpa only [zero_smul,zero_sub,neg_mul,one_mul] using H

lemma splitNormalAction_source_gradient {x : M} {p v : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hv : t • v ∈ injectivityDomain x)
    (hB : DifferentiableAt ℝ (splitNormalAction x t p) (0,v))
    (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (splitNormalAction x t p) (0,v) (xi,0) = -inner ℝ v xi := by
  have hnc := ((normalCost_contDiffAt hv).differentiableAt (by simp)).hasFDerivAt
  have H := (hnc.mul_const t⁻¹).add_const
    (cost (riemannianExp x (t • v)) (riemannianExp x p)/(1-t))
  have hp₀ := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const v (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have H' : HasFDerivAt (fun u => splitNormalAction x t p (u,v))
      (t⁻¹ • fderiv ℝ (normalCost x (t • v)) 0) 0 := by
    simpa only [splitNormalAction,normalCost,div_eq_mul_inv] using H
  have heq := (hB.hasFDerivAt.comp (f := fun u => (u,v)) 0 hp₀).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A xi) heq
  change fderiv ℝ (splitNormalAction x t p) (0,v) (xi,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • v)) 0 xi at hh
  rw [normalCost_fderiv_zero hv,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma splitNormalAction_mixed_pairing {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hleft : t • p ∈ injectivityDomain x)
    (hright : (1-t) • (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (xi k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (xi,0) (0,k) = -inner ℝ k xi := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := splitNormalAction x t p
  have hBc : ContDiffAt ℝ ∞ B (0,p) :=
    (splitNormalAction_contDiffAt hleft hright).comp (f := fun q : V×V => (p,q)) (0,p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB₂ := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdf := (hB₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := ((hdf.hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
    (hasFDerivAt_const (xi,(0:V)) p)).fderiv
  have hnB : ∀ᶠ v : V in 𝓝 p, DifferentiableAt ℝ B (0,v) := by
    have hn := (hBc.of_le (m := 1) (by simp)).eventually (by norm_num)
    exact (hL.continuousAt.eventually hn).mono (fun _ h => h.differentiableAt (by norm_num))
  have hscale : Continuous (fun v : V => t • v) := by fun_prop
  have hnleft : ∀ᶠ v : V in 𝓝 p, t • v ∈ injectivityDomain x :=
    hscale.continuousAt.preimage_mem_nhds
      ((isOpen_injectivityDomain x).mem_nhds hleft)
  have heq : (fun v : V => fderiv ℝ B (0,v) (xi,0)) =ᶠ[𝓝 p]
      (fun v : V => -inner ℝ v xi) := by
    filter_upwards [hnB,hnleft] with v hv hvleft
    exact splitNormalAction_source_gradient ht hvleft hv xi
  have hinner : HasFDerivAt (fun v : V => -inner ℝ v xi) (-(innerSL ℝ xi)) p := by
    convert! ((innerSL ℝ xi).hasFDerivAt (x := p)).neg using 1
    funext v
    exact congrArg Neg.neg (real_inner_comm xi v)
  have H := congrArg (fun A : V →L[ℝ] ℝ => A k) (hd.symm.trans (heq.fderiv_eq.trans hinner.fderiv))
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,neg_apply] at H
  change fderiv ℝ (fderiv ℝ B) (0,p) (0,k) (xi,0) = -inner ℝ xi k at H
  rw [real_inner_comm] at H
  rwa [(hB₂.isSymmSndFDerivAt (by simp)).eq] at H

end WeakMTWTransport

end

end OAI
