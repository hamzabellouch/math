import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricSegmentsFromMidpoints
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RiemannianApproximateMidpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.MinimizingLieMetric
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! # Constructing the proper minimizing metric on the Lie model -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] [LocallyCompactSpace G]

def leftRiemannianMinimizingMetric (e : E ≃L[ℝ] F) : ProperMinimizingMetric G where
  metric := leftRiemannianMetric (G := G) e
  topology_eq := leftRiemannianMetric_topology e
  proper := leftRiemannianMetric_proper e
  leftInvariant := leftRiemannianMetric_isometric e
  minimizing := by
    let metric := leftRiemannianMetric (G := G) e
    let proper := leftRiemannianMetric_proper (G := G) e
    intro g
    exact exists_metric_segment (leftRiemannianMetric_approximateMidpoints e) 1 g

def SimplyConnectedSolvableLieModel.minimizingMetric (S : SimplyConnectedSolvableLieModel) :
    ProperMinimizingMetric S.carrier := by
  let groupTopology : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ∞
  let localCompact : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  let e : S.modelSpace ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S.modelSpace)) :=
    (Module.finBasis ℝ S.modelSpace).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ S.modelSpace)) ℝ).symm
  exact leftRiemannianMinimizingMetric e

theorem lieMinimizingMetricInput : LieMinimizingMetricInput :=
  fun S => ⟨S.minimizingMetric⟩

end PolycyclicRecognition

end

end OAI
