import OAI.GroupTheory.PolycyclicRecognition.Algebra.LeftInvariantRiemannianLength
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConnectedEMetric
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # The compatible metric induced by the left-invariant Riemannian structure -/

noncomputable section
namespace PolycyclicRecognition

open Bundle
open scoped Manifold ContDiff Bundle

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] (e : E ≃L[ℝ] F)

abbrev leftRiemannianEMetric : EMetricSpace G := by
  letI := leftRiemannianBundle (G := G) e
  letI : IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous,
      fun _ _ _ => rfl⟩⟩
  exact EMetricSpace.ofRiemannianMetric (𝓘(ℝ, E)) G

theorem leftRiemannianEMetric_topology :
    (leftRiemannianEMetric (G := G) e).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace G› := rfl

abbrev leftRiemannianMetric [ConnectedSpace G] : MetricSpace G := by
  letI := leftRiemannianEMetric (G := G) e
  exact EMetricSpace.toMetricSpace edist_ne_top_of_connected

theorem leftRiemannianMetric_topology [ConnectedSpace G] :
    (leftRiemannianMetric (G := G) e).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace G› := rfl

theorem leftRiemannianMetric_isometric [ConnectedSpace G] :
    letI := leftRiemannianMetric (G := G) e
    IsIsometricSMul G G := by
  let := leftRiemannianMetric (G := G) e
  refine ⟨fun g => ?_⟩
  intro x y
  exact riemannianEDist_leftTranslation e g x y

end PolycyclicRecognition

end

end OAI
