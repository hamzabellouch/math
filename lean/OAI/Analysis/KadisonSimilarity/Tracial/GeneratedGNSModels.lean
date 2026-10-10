import OAI.Analysis.KadisonSimilarity.Tracial.TracialSubalgebraModels
import OAI.Analysis.KadisonSimilarity.Tracial.TracialGeneratedAlgebra

namespace OAI

/-! The algebra generated inside a tracial ambient algebra has its own
canonical GNS model. Ambient algebra-vector density gives native factor
generation, and scalar freeness and faithful vectors restrict directly. -/

noncomputable section
namespace KadisonSimilarity

open TracialCornerGeometry
open scoped ComplexOrder

variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (A D L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

/-- Ordinary ambient L² generation becomes factor generation in the
canonical GNS space of the generated algebra, without changing models. -/
theorem restrictedGNS_factorsTraciallyGenerate (hA : A ≤ L) (hD : D ≤ L)
    (hdense : ∀ a : L, gnsTracialVector τ (a : P) ∈
      closure (Set.range ((gnsTracialVector τ).comp
        (factorAlgebra A D).subtype.toLinearMap))) :
    (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr)).FactorsTraciallyGenerate
        (A.comap L.subtype) (D.comap L.subtype) := by
  let S := factorAlgebra (A.comap L.subtype) (D.comap L.subtype)
  let J := restrictedTracialGNSInclusion τ L
  let F := (gnsTracialVector (restrictedPositiveTrace τ L)).comp S.subtype.toLinearMap
  have hm : S.map L.subtype = factorAlgebra A D := factorAlgebra_map_subtype A D L hA hD
  have hsubset : Set.range ((gnsTracialVector τ).comp (factorAlgebra A D).subtype.toLinearMap) ⊆
      J '' Set.range F := by
    rintro ξ ⟨b, rfl⟩
    have hb : (b : P) ∈ S.map L.subtype := by rw [hm]; exact b.property
    obtain ⟨c, hc, hcb⟩ := hb
    refine ⟨gnsTracialVector (restrictedPositiveTrace τ L) c, ?_, ?_⟩
    · exact ⟨⟨c, hc⟩, rfl⟩
    · change J (gnsTracialVector (restrictedPositiveTrace τ L) c) = gnsTracialVector τ (b : P)
      rw [restrictedTracialGNSInclusion_vector]
      exact congrArg (gnsTracialVector τ) hcb
  have hv (a : L) : gnsTracialVector (restrictedPositiveTrace τ L) a ∈
      closure (Set.range F) := by
    rw [J.isometry.isEmbedding.closure_eq_preimage_closure_image]
    change J (gnsTracialVector (restrictedPositiveTrace τ L) a) ∈ closure (J '' Set.range F)
    rw [restrictedTracialGNSInclusion_vector]
    exact closure_mono hsubset (hdense a)
  change Dense (Set.range F)
  intro ξ
  exact (gnsTracialVector_dense (restrictedPositiveTrace τ L)).induction_on ξ
    isClosed_closure hv

/-- Freeness of the two ambient factors restricts to the canonical trace
of the generated subalgebra. -/
theorem restrictedGNS_scalarFree (hfree : ScalarFree τ.toLinearMap A D) :
    ScalarFree
      (gnsTracialGeometry (restrictedPositiveTrace τ L)
        (restrictedPositiveTrace_tracial τ L htr)).trace
      (A.comap L.subtype) (D.comap L.subtype) := by
  change ScalarFree (τ.toLinearMap.comp L.subtype.toLinearMap)
    (A.comap L.subtype) (D.comap L.subtype)
  exact scalarFree_subtype τ.toLinearMap A D L hfree

/-- Faithfulness of the ambient trace makes the native generated-algebra
GNS vectors injective. -/
theorem restrictedGNS_vector_injective
    (hf : ∀ a : P, τ (star a * a) = 0 → a = 0) :
    Function.Injective
      (gnsTracialGeometry (restrictedPositiveTrace τ L)
        (restrictedPositiveTrace_tracial τ L htr)).vector :=
  gnsTracialVector_injective (restrictedPositiveTrace τ L)
    (restrictedPositiveTrace_faithful τ L hf)

end KadisonSimilarity

end

end OAI
