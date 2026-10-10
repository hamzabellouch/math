import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.TransverseConcavity
import OAI.Analysis.BiholderTransport.Regularity.ContDiffUncurryIterated
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost

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

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_hessian_branch {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ A : TangentSpace 𝓘(ℝ,Model n) x → ℝ, ContDiffAt ℝ ∞ A p ∧
      ∀ᶠ w in 𝓝 p, w ∈ injectivityDomain x → hessianValue x w xi=A w := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  obtain ⟨G,hG,hagree⟩ := exists_smooth_cost_branch (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  let A : V → ℝ := fun w => iteratedDeriv 2 (fun s : ℝ => G (riemannianExp x (s • xi),riemannianExp x w)) 0
  have hG' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
      (riemannianExp x ((0:ℝ) • xi),riemannianExp x p) := by
    simpa only [zero_smul,riemannianExp_zero] using hG
  have hLs : ContMDiffAt 𝓘(ℝ,V×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : V×ℝ => riemannianExp x (q.2 • xi)) (p,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (p,0) (contDiffAt_snd.smul contDiffAt_const).contMDiffAt
  have hLw : ContMDiffAt 𝓘(ℝ,V×ℝ) 𝓘(ℝ,Model n) ∞
      (fun q : V×ℝ => riemannianExp x q.1) (p,0) :=
    (contMDiff_riemannianExp_fiber x _).comp (p,0) contDiffAt_fst.contMDiffAt
  have hGA : ContDiffAt ℝ ∞ (fun q : V×ℝ => G (riemannianExp x (q.2 • xi),riemannianExp x q.1)) (p,0) :=
    (hG'.comp (p,0) (hLs.prodMk hLw)).contDiffAt
  refine ⟨A,contDiffAt_iteratedDeriv_parameter hGA 2,?_⟩
  have hinc : Continuous (fun w : V => (⟨x,w⟩ : TangentBundle 𝓘(ℝ,Model n) M)) :=
    FiberBundle.continuous_totalSpaceMk (Model n) (fun y : M => TangentSpace 𝓘(ℝ,Model n) y) x
  filter_upwards [hinc.continuousAt.eventually hagree] with w hw
  intro hwID
  have hcost := hw hwID
  have hcurve : ContinuousAt (fun s : ℝ => (riemannianExp x (s • xi),riemannianExp x w)) 0 :=
    ((contMDiff_riemannianExp_fiber x).continuous.continuousAt.comp
      (show ContinuousAt (fun s : ℝ => s • xi) 0 from by fun_prop)).prodMk continuousAt_const
  have hcurve' : Tendsto (fun s : ℝ => (riemannianExp x (s • xi),riemannianExp x w)) (𝓝 0)
      (𝓝 (x,riemannianExp x w)) := by simpa only [zero_smul,riemannianExp_zero] using hcurve.tendsto
  exact Filter.EventuallyEq.iteratedDeriv_eq 2 (hcost.comp_tendsto hcurve')

lemma nonconjugate_inward_hessian_bounded {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x)
    (hreg : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)) (xi : TangentSpace 𝓘(ℝ,Model n) x) :
    ∃ C : ℝ, ∀ᶠ r : ℝ in 𝓝[<] 1, |hessianValue x (r • p) xi|≤C := by
  obtain ⟨A,hA,hagree⟩ := exists_smooth_hessian_branch hreg xi
  have hline : Tendsto (fun r : ℝ => r • p) (𝓝[<] 1) (𝓝 p) := by
    simpa only [one_smul] using
      (show ContinuousAt (fun r : ℝ => r • p) 1 from by fun_prop).tendsto.mono_left nhdsWithin_le_nhds
  have hb := ((hA.continuousAt.abs.tendsto).comp hline).eventually_lt_const (show |A p| < |A p|+1 by linarith)
  refine ⟨|A p|+1,?_⟩
  filter_upwards [hline.eventually hagree,hb,
    (eventually_gt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hr hrB hr0 hr1
  rw [hr (contracted_minimizer_mem_injectivityDomain hp hr0 hr1)]
  exact hrB.le
end WeakMTWTransport

end

end OAI
