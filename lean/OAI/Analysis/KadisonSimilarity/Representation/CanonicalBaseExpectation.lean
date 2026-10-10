import OAI.Analysis.KadisonSimilarity.Tracial.TracialEmbeddingBalls
import OAI.Analysis.KadisonSimilarity.Representation.CanonicalGeneratedModel

namespace OAI

/-! The first-factor expectation in the canonical generated algebra follows
from bounded trace-vector closure in the original factor. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
  (τA : A →ₚ[ℂ] ℂ) (hφτ : ∀ a, τ (φ a) = τA a)
  (hi : Function.Injective φ)

local notation "G" => canonicalGeneratedGeometry τ htr φ ψ

include hi hφτ in
theorem canonicalFirstRange_expectation
    (hc : ∀ C : ℝ, IsClosed (gnsTracialVector τA '' Metric.closedBall (0 : A) C))
    (h1 : τ 1 = 1) (hf : ∀ a : P, τ (star a * a) = 0 → a = 0)
    (hnormal : ∃ N : VonNeumannAlgebra (canonicalGeneratedTrace τ htr φ ψ).GNS,
      (G).left.range = N.toStarSubalgebra) :
    Nonempty (TracialExpectation (G).trace (canonicalGeneratedFirst τ htr φ ψ).range) := by
  obtain ⟨N, hN⟩ := hnormal
  have hi' : Function.Injective (canonicalGeneratedFirst τ htr φ ψ) := by
    intro a b h
    exact hi (congrArg (fun x : canonicalGeneratedAlgebra τ htr φ ψ => (x : P)) h)
  exact tracialRange_expectation τA (G) (canonicalGeneratedFirst τ htr φ ψ)
    hφτ hi' hc h1 (canonicalGenerated_faithful τ htr φ ψ hf) N hN

end KadisonSimilarity

end

end OAI
