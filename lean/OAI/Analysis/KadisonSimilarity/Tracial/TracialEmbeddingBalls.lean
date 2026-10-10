import OAI.Analysis.KadisonSimilarity.Tracial.TracialEmbeddingTransport
import OAI.Analysis.KadisonSimilarity.Representation.SubalgebraNormality
import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialExpectations

namespace OAI

/-! Closed bounded trace-vector sets transfer through a trace-preserving
embedding, giving normality and expectation onto its actual range. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped CStarAlgebra ComplexOrder

variable {R P H : Type*} [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder R] [StarOrderedRing R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : R →ₚ[ℂ] ℂ) (G : TracialCornerGeometry P H)
  (φ : R →⋆ₐ[ℂ] P) (hφ : ∀ a, G.trace (φ a) = τ a)
  (hi : Function.Injective φ)

include hφ hi in
theorem tracialRange_trace_balls_closed
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : R) C))
    (C : ℝ) : IsClosed ((G.vector.comp φ.range.subtype.toLinearMap) ''
      Metric.closedBall (0 : φ.range) C) := by
  let j := (G.baseInclusion φ.range).comp (tracialRangeIsometry τ G φ hφ)
  have hj (a : R) : j (gnsTracialVector τ a) = G.vector (φ a) := by
    change (G.baseInclusion φ.range) (tracialRangeIsometry τ G φ hφ (gnsTracialVector τ a)) = _
    rw [tracialRangeIsometry_vector]
    rfl
  have hn (a : R) : ‖φ a‖ = ‖a‖ := (NonUnitalStarAlgHom.isometry φ hi).norm_map_of_map_zero
    (map_zero φ) a
  have heq : (G.vector.comp φ.range.subtype.toLinearMap) ''
      Metric.closedBall (0 : φ.range) C =
      j '' (gnsTracialVector τ '' Metric.closedBall (0 : R) C) := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      change φ b = (a : P) at hb
      refine ⟨gnsTracialVector τ b, ⟨b, ?_, rfl⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
        rw [← hn, hb]
        exact ha
      · rw [hj, hb]
        rfl
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨φ.rangeRestrict a, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right] at ha ⊢
        change ‖φ a‖ ≤ C
        rwa [hn]
      · exact (hj a).symm
  rw [heq]
  exact j.isometry.isClosedEmbedding.isClosedMap _ (hc C)

include hφ hi in
theorem tracialRange_normal [IsClosed (φ.range : Set P)]
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : R) C)) :
    φ.range.map G.left =
      (representationVonNeumannAlgebra (G.left.comp φ.range.subtype)).toStarSubalgebra := by
  exact G.subalgebra_normal_range_of_closed_trace_balls φ.range
    (tracialRange_trace_balls_closed τ G φ hφ hi hc)

include hφ hi in
theorem tracialRange_expectation
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : R) C))
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (M : VonNeumannAlgebra H) (hrange : G.left.range = M.toStarSubalgebra) :
    Nonempty (TracialExpectation G.trace φ.range) := by
  let : IsClosed (φ.range : Set P) := (NonUnitalStarAlgHom.isometry φ hi).isClosedEmbedding.isClosed_range
  exact G.tracialExpectation_of_normal_range h1 hf M hrange φ.range _
    (tracialRange_normal τ G φ hφ hi hc)

end KadisonSimilarity

end

end OAI
