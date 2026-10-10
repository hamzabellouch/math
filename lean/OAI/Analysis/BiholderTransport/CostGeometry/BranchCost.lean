import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.TotalInjectivity
import OAI.Analysis.BiholderTransport.Coordinates.BranchInverse

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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_cost_branch (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ G : M×M → ℝ,
      ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞ G
        (z.1,riemannianExp z.1 z.2) ∧
      ∀ᶠ r in 𝓝 z, r.2 ∈ injectivityDomain r.1 →
        (fun q : M×M => cost q.1 q.2) =ᶠ[𝓝 (r.1,riemannianExp r.1 r.2)] G := by
  obtain ⟨P,hP,hPz,hleft,hright⟩ := exists_smooth_exp_branch z hz
  let G : M×M → ℝ := fun q => ‖(P q).2‖^2/2
  refine ⟨G,(contMDiff_tangent_energy (P (z.1,riemannianExp z.1 z.2))).comp _ hP,?_⟩
  let F : TangentBundle 𝓘(ℝ,Model n) M → M×M := fun r => (r.1,riemannianExp r.1 r.2)
  have hF : Continuous F :=
    ((Bundle.contMDiff_proj (fun v : M => TangentSpace 𝓘(ℝ,Model n) v)).prodMk contMDiff_riemannianExp).continuous
  have hPnear : ∀ᶠ q in 𝓝 (F z), ContinuousAt P q := by
    have hzero : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
        (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 0 P (F z) := hP.of_le bot_le
    exact ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hzero).mono
      (fun point hpoint => hpoint.continuousAt)
  have hRnear : ∀ᶠ q in 𝓝 (F z), ∀ᶠ q' in 𝓝 q,
      (P q').1=q'.1 ∧ riemannianExp (P q').1 (P q').2=q'.2 :=
    eventually_eventually_nhds.mpr hright
  filter_upwards [hleft,(hF.continuousAt.eventually (hPnear.and hRnear))] with r hr hnear
  intro hrID
  have hC : {v : TangentBundle 𝓘(ℝ,Model n) M | v.2 ∈ minimizingVectors v.1} ∈ 𝓝 (P (F r)) := by
    rw [show P (F r)=r from hr]
    exact mem_interior_iff_mem_nhds.mp (interior_total_minimizingVectors r hrID)
  have hmin := hnear.1.preimage_mem_nhds hC
  filter_upwards [hmin,hnear.2] with q hqmin hq
  change dist q.1 q.2^2/2=‖(P q).2‖^2/2
  change dist (P q).1 (riemannianExp (P q).1 (P q).2)=‖(P q).2‖ at hqmin
  have hd : dist q.1 q.2=‖(P q).2‖ :=
    (congrArg₂ dist hq.1.symm hq.2.symm).trans hqmin
  rw [hd]
end WeakMTWTransport

end

end OAI
