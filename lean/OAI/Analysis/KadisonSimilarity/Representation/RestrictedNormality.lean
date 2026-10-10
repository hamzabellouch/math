import OAI.Analysis.KadisonSimilarity.Tracial.TracialBoundedBalls
import OAI.Analysis.KadisonSimilarity.Representation.CanonicalGeneratedModel

namespace OAI

/-! The canonical GNS model of a bounded L²-generated algebra is normal.
The proof uses the actual inclusion of its trace vectors in the ambient
GNS space. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a * b) = τ (b * a))

theorem restricted_generated_trace_balls_closed
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) (C : ℝ) :
    let L := (gnsTracialGeometry τ htr).l2GeneratedAlgebra S
    IsClosed (gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C) := by
  let G := gnsTracialGeometry τ htr
  let L := G.l2GeneratedAlgebra S
  let J := restrictedTracialGNSInclusion τ L
  change IsClosed (gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C)
  have heq : gnsTracialVector (restrictedPositiveTrace τ L) '' Metric.closedBall (0 : L) C =
      J ⁻¹' (gnsTracialVector τ '' Metric.closedBall (0 : A) C) := by
    ext ξ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : A), ha, (restrictedTracialGNSInclusion_vector τ L a).symm⟩
    · rintro ⟨a, ha, hξ⟩
      have hJξ : J ξ ∈ G.baseSpace L := by
        change J ξ ∈ ((gnsTracialGeometry τ htr).baseSpace L : Set τ.GNS)
        rw [← restrictedTracialGNSInclusion_range τ L htr]
        exact ⟨ξ, rfl⟩
      have hmem : a ∈ L := by
        change G.vector a ∈ G.baseSpace S.topologicalClosure
        change G.vector a = J ξ at hξ
        rw [hξ, G.baseSpace_topologicalClosure]
        exact (le_of_eq (G.baseSpace_l2GeneratedAlgebra S)) hJξ
      refine ⟨⟨a, hmem⟩, ha, ?_⟩
      apply J.injective
      exact (restrictedTracialGNSInclusion_vector τ L ⟨a, hmem⟩).trans hξ
  rw [heq]
  exact (hc C).preimage J.continuous

theorem restricted_generated_normal_range
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (S : StarSubalgebra ℂ A) :
    let L := (gnsTracialGeometry τ htr).l2GeneratedAlgebra S
    (restrictedPositiveTrace τ L).gnsStarAlgHom.range =
      (representationVonNeumannAlgebra (restrictedPositiveTrace τ L).gnsStarAlgHom).toStarSubalgebra := by
  dsimp only
  exact (gnsTracialGeometry _ (restrictedPositiveTrace_tracial τ _ htr)).normal_range_of_closed_trace_balls
    (restricted_generated_trace_balls_closed τ htr hc S)

variable {B R : Type*} [CStarAlgebra B] [CStarAlgebra R]

theorem canonicalGenerated_normal_range
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τ '' Metric.closedBall (0 : A) C))
    (φ : B →⋆ₐ[ℂ] A) (ψ : R →⋆ₐ[ℂ] A) :
    (canonicalGeneratedGeometry τ htr φ ψ).left.range =
      (representationVonNeumannAlgebra (canonicalGeneratedGeometry τ htr φ ψ).left).toStarSubalgebra :=
  restricted_generated_normal_range τ htr hc (factorAlgebra φ.range ψ.range)

end KadisonSimilarity

end

end OAI
