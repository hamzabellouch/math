import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.InjectivityOpen
import OAI.Analysis.BiholderTransport.Coordinates.JointExpInverse
import OAI.Analysis.BiholderTransport.Regularity.InteriorCompactUniqueFiber

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

section
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma joint_exp_locally_injective (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    ∃ U : Set (TangentBundle 𝓘(ℝ,Model n) M), IsOpen U ∧ z ∈ U ∧
      InjOn (fun q : TangentBundle 𝓘(ℝ,Model n) M => (q.1,riemannianExp q.1 q.2)) U := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) z
  let d := extChartAt 𝓘(ℝ,Model n) (riemannianExp z.1 z.2)
  obtain ⟨e,he,hze,_,_,_,_⟩ := exists_joint_exp_inverse z hz
  let U := χ.source ∩ χ ⁻¹' e.source
  have hU : IsOpen U := (continuousOn_extChartAt z).isOpen_inter_preimage (isOpen_extChartAt_source z) e.open_source
  refine ⟨U,hU,⟨mem_extChartAt_source z,hze⟩,?_⟩
  intro q hq r hr hqr
  apply χ.injOn hq.1 hr.1
  apply e.injOn hq.2 hr.2
  rw [he]
  change ((χ q).1,d (riemannianExp (χ.symm (χ q)).1 (χ.symm (χ q)).2)) =
    ((χ r).1,d (riemannianExp (χ.symm (χ r)).1 (χ.symm (χ r)).2))
  rw [χ.left_inv hq.1,χ.left_inv hr.1]
  apply Prod.ext
  · simp only [χ,tangent_chart_apply]
    exact congrArg (extChartAt 𝓘(ℝ,Model n) z.1) (congrArg Prod.fst hqr)
  · exact congrArg d (congrArg Prod.snd hqr)

lemma interior_total_minimizingVectors (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : z.2 ∈ injectivityDomain z.1) :
    z ∈ interior {q : TangentBundle 𝓘(ℝ,Model n) M | q.2 ∈ minimizingVectors q.1} := by
  apply interior_of_compact_unique_fiber isCompact_total_minimizingVectors
    ((FiberBundle.continuous_proj _ _).prodMk contMDiff_riemannianExp.continuous)
  · intro y
    obtain ⟨p,hp,he⟩ := exists_minimizing_vector (n := n) y.1 y.2
    exact ⟨⟨y.1,p⟩,hp,Prod.ext rfl he⟩
  · rintro ⟨b,v⟩ hv hqz
    rcases z with ⟨a,u⟩
    have hba : b=a := congrArg Prod.fst hqz
    subst b
    have huv : u=v := riemannianExp_interior_unique hz hv (congrArg Prod.snd hqz).symm
    subst v
    rfl
  · exact joint_exp_locally_injective z hz

lemma total_injectivityDomain_eq_interior :
    {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} =
      interior {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ minimizingVectors z.1} := by
  apply subset_antisymm
  · exact fun z hz => interior_total_minimizingVectors z hz
  · intro z hz
    apply interior_minimizingVectors_subset z.1
    apply mem_interior_iff_mem_nhds.mpr
    exact (FiberBundle.continuous_totalSpaceMk (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) z.1).continuousAt.preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp hz)

lemma isOpen_total_injectivityDomain :
    IsOpen {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ injectivityDomain z.1} := by
  rw [total_injectivityDomain_eq_interior]
  exact isOpen_interior

end
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma contMDiff_tangent_energy :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun z : TangentBundle 𝓘(ℝ,E) M => ‖z.2‖^2/2) := by
  intro z
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) z
  have hbase : (χ z).1 ∈ (extChartAt 𝓘(ℝ,E) z.1).target :=
    (extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1)
  have hg := (contDiffOn_riemannianCoordinateMetric z.1).contDiffAt
    ((isOpen_extChartAt_target z.1).mem_nhds hbase)
  have henergy : ContDiffAt ℝ ∞
      (fun q : E×E => riemannianCoordinateMetric z.1 q.1 q.2 q.2/2) (χ z) :=
    (((hg.comp (χ z) contDiffAt_fst).clm_apply contDiffAt_snd).clm_apply contDiffAt_snd).div_const 2
  apply (henergy.contMDiffAt.comp z (show ContMDiffAt
    (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ z from contMDiffAt_extChartAt)).congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ,E).prod 𝓘(ℝ,E)) z] with q hq
  exact congrArg (fun a : ℝ => a/2) (coordinate_spray_energy z q ((tangent_chart_source_iff z q).mp hq)).symm

end WeakMTWTransport

end

end OAI
