import OAI.Analysis.KadisonSimilarity.Tracial.GeneratedGNSModels

namespace OAI

/-! The actual copies of the two factors inside their generated algebra.
The range identifications align the GNS recovery operator with the factor
generation, freeness, and matrix tower used by the local theorem. -/

noncomputable section
namespace KadisonSimilarity
open TracialCornerGeometry
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (L : StarSubalgebra ℂ P) [IsClosed (L : Set P)]

omit [PartialOrder P] [StarOrderedRing P] in
theorem range_codRestrict_eq_comap (φ : A →⋆ₐ[ℂ] P) (hφ : ∀ a, φ a ∈ L) :
    (φ.codRestrict L hφ).range = φ.range.comap L.subtype := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

omit [PartialOrder P] [StarOrderedRing P] in
theorem codRestrict_range_isClosed (φ : A →⋆ₐ[ℂ] P) (hφ : ∀ a, φ a ∈ L)
    (hclosed : IsClosed (φ.range : Set P)) :
    IsClosed ((φ.codRestrict L hφ).range : Set L) := by
  rw [range_codRestrict_eq_comap]
  exact hclosed.preimage continuous_subtype_val

theorem generatedEmbeddings_factorsTraciallyGenerate
    (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
    (hφ : ∀ a, φ a ∈ L) (hψ : ∀ r, ψ r ∈ L)
    (hdense : ∀ a : L, gnsTracialVector τ (a : P) ∈
      closure (Set.range ((gnsTracialVector τ).comp
        (factorAlgebra φ.range ψ.range).subtype.toLinearMap))) :
    (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr)).FactorsTraciallyGenerate
      (φ.codRestrict L hφ).range (ψ.codRestrict L hψ).range := by
  rw [range_codRestrict_eq_comap, range_codRestrict_eq_comap]
  apply restrictedGNS_factorsTraciallyGenerate τ htr φ.range ψ.range L _ _ hdense
  · rintro _ ⟨a, rfl⟩; exact hφ a
  · rintro _ ⟨r, rfl⟩; exact hψ r

theorem generatedEmbeddings_scalarFree
    (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)
    (hφ : ∀ a, φ a ∈ L) (hψ : ∀ r, ψ r ∈ L)
    (hfree : ScalarFree τ.toLinearMap φ.range ψ.range) :
    ScalarFree (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr)).trace
      (φ.codRestrict L hφ).range (ψ.codRestrict L hψ).range := by
  rw [range_codRestrict_eq_comap, range_codRestrict_eq_comap]
  exact restrictedGNS_scalarFree τ htr φ.range ψ.range L hfree

variable [PartialOrder R] [StarOrderedRing R]
  (τR : R →ₚ[ℂ] ℂ) (ψ : R →⋆ₐ[ℂ] P) (hψ : ∀ r, ψ r ∈ L)
  (htrace : ∀ r, τ (ψ r) = τR r)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

include htrace in
omit [StarOrderedRing R] in
theorem generatedEmbedding_preserves_trace :
    ∀ r, (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr)).trace (ψ.codRestrict L hψ r) = τR r :=
  htrace

/-- The matrix tower lives on the same native GNS space as the recovered
operator, and on the exact range of the embedded free factor. -/
def generatedEmbeddingMatrices
    (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR)) :=
  transportTracialMatrices τR
    (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr))
    (ψ.codRestrict L hψ) (generatedEmbedding_preserves_trace τ htr L τR ψ hψ htrace) M

def generatedEmbeddingRealSequence (S : RealTracialSequence τR.toLinearMap) :=
  transportRealTracialSequence τR
    (gnsTracialGeometry (restrictedPositiveTrace τ L)
      (restrictedPositiveTrace_tracial τ L htr))
    (ψ.codRestrict L hψ) (generatedEmbedding_preserves_trace τ htr L τR ψ hψ htrace) S

end KadisonSimilarity

end

end OAI
