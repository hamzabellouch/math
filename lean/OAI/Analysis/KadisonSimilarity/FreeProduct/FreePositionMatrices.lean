import OAI.Analysis.KadisonSimilarity.Tracial.PopaConjugatePosition

namespace OAI

/-! The published conjugacy input is used once, for the prescribed
irreducible inclusion. Its concrete conjugated copy retains the original
matrix tower and real orthonormal sequence. -/

noncomputable section
namespace KadisonSimilarity
open HochschildUltrapower
open scoped ComplexOrder

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder R] [StarOrderedRing R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ) (τR : R →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b : A, τA (a * b) = τA (b * a))
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]

local notation "G" => gnsTracialGeometry (quotientTrace τB hB ω trB)
  (quotientTrace_tracial τB hB ω trB)

omit [∀ j, Nonempty (I j)] in
/-- Conditional free position with all matrix-density data retained. The
only freeness assumption is the stated Popa specialization; none of the
operator estimates of the present manuscript occurs in it. -/
theorem exists_conjugated_free_matrix_copy
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (ρ : R →⋆ₐ[ℂ] A) (hρ : Function.Injective ρ)
    (hρτ : ∀ x, τA (ρ x) = τR x)
    (hfA : ∀ a : A, τA (star a * a) = 0 → a = 0)
    (M : NestedTracialMatrices (A := I) τR.toLinearMap (gnsTracialVector τR))
    (S : RealTracialSequence τR.toLinearMap)
    (published : Popa1995ConjugateFreenessInput τA τB hA hB ω trA trB φ hφ hω ρ) :
    ∃ ψ : R →⋆ₐ[ℂ] Ultrapower τB hB ω trB,
      Function.Injective ψ ∧ IsClosed (ψ.range : Set (Ultrapower τB hB ω trB)) ∧
      ψ.range ≤ (tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ).range ∧
      ScalarFree (quotientTrace τB hB ω trB).toLinearMap
        (constant τB hB ω trB).range ψ.range ∧
      (∀ x, (quotientTrace τB hB ω trB) (ψ x) = τR x) ∧
      Nonempty (NestedTracialMatrices (A := I)
        ((G).trace.comp ψ.range.subtype.toLinearMap) ((G).baseVector ψ.range)) ∧
      Nonempty (RealTracialSequence ((G).trace.comp ψ.range.subtype.toLinearMap)) := by
  obtain ⟨u, hu⟩ := published
  let ψ := conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ u
  have hψτ : ∀ x, (G).trace (ψ x) = τR x := by
    intro x
    exact (conjugatedConstantEmbedding_trace τA τB hA hB ω trA trB φ hφ ρ u x).trans
      (hρτ x)
  refine ⟨ψ, conjugatedConstantEmbedding_injective τA τB hA hB ω trA trB φ hφ
      ρ hρ hfA u,
    conjugatedConstantEmbedding_range_isClosed τA τB hA hB ω trA trB φ hφ
      ρ hρ hfA u,
    conjugatedConstantEmbedding_range_le τA τB hA hB ω trA trB φ hφ ρ u,
    hu, hψτ, ?_, ?_⟩
  · exact ⟨transportTracialMatrices τR (G) ψ hψτ M⟩
  · exact ⟨transportRealTracialSequence τR (G) ψ hψτ S⟩

end KadisonSimilarity

end

end OAI
