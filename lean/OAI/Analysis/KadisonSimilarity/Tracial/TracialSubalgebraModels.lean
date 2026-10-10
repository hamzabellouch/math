import OAI.Analysis.KadisonSimilarity.Tracial.TracialEmbeddingTransport
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialHomCompression

namespace OAI

/-! The normal algebra generated inside the ultrapower is represented on
its own tracial GNS space. Restriction of the positive trace and its exact
Hilbert-space identification require no further analytic input. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

/-- Restrict the actual positive functional to a closed star subalgebra. -/
def restrictedPositiveTrace : L →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (τ.toLinearMap.comp L.subtype.toLinearMap)
    (fun _a ha => τ.map_nonneg ha)

@[simp] theorem restrictedPositiveTrace_apply (a : L) :
    restrictedPositiveTrace τ L a = τ (a : P) := rfl

theorem restrictedPositiveTrace_one (h1 : τ 1 = 1) :
    restrictedPositiveTrace τ L 1 = 1 := h1

theorem restrictedPositiveTrace_tracial
    (htr : ∀ a b : P, τ (a * b) = τ (b * a)) (a b : L) :
    restrictedPositiveTrace τ L (a * b) = restrictedPositiveTrace τ L (b * a) :=
  htr a b

theorem restrictedPositiveTrace_faithful
    (hf : ∀ a : P, τ (star a * a) = 0 → a = 0)
    (a : L) (ha : restrictedPositiveTrace τ L (star a * a) = 0) : a = 0 := by
  apply Subtype.ext
  exact hf a ha

/-- The inclusion of the generated algebra induces its concrete GNS inclusion. -/
def restrictedTracialGNSInclusion :
    (restrictedPositiveTrace τ L).GNS →ₗᵢ[ℂ] τ.GNS :=
  gnsTracialHomIsometry (restrictedPositiveTrace τ L) τ L.subtype (fun _ => rfl)

@[simp] theorem restrictedTracialGNSInclusion_vector (a : L) :
    restrictedTracialGNSInclusion τ L (gnsTracialVector (restrictedPositiveTrace τ L) a) =
      gnsTracialVector τ (a : P) :=
  gnsTracialHomIsometry_vector (restrictedPositiveTrace τ L) τ L.subtype (fun _ => rfl) a

/-- Its range is exactly the completed algebra-vector subspace. -/
theorem restrictedTracialGNSInclusion_range
    (htr : ∀ a b : P, τ (a * b) = τ (b * a)) :
    Set.range (restrictedTracialGNSInclusion τ L) =
      ((gnsTracialGeometry τ htr).baseSpace L : Set τ.GNS) := by
  let J := restrictedTracialGNSInclusion τ L
  have hc : IsClosed (Set.range J) := J.isometry.isClosedEmbedding.isClosed_range
  apply Set.Subset.antisymm
  · rintro _ ⟨ξ, rfl⟩
    refine (gnsTracialVector_dense (restrictedPositiveTrace τ L)).induction_on ξ
      (((gnsTracialGeometry τ htr).baseSpace L).isClosed.preimage J.continuous) ?_
    intro a
    rw [restrictedTracialGNSInclusion_vector]
    exact ((gnsTracialGeometry τ htr).baseVector L a).property
  · change closure (Set.range ((gnsTracialGeometry τ htr).baseAlgebraVectors L)) ⊆ _
    apply closure_minimal _ hc
    rintro _ ⟨a, rfl⟩
    exact ⟨gnsTracialVector (restrictedPositiveTrace τ L) a,
      restrictedTracialGNSInclusion_vector τ L a⟩

end KadisonSimilarity

end

end OAI
