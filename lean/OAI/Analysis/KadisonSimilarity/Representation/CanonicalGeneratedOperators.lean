import OAI.Analysis.KadisonSimilarity.Representation.CanonicalGeneratedModel
import OAI.Analysis.KadisonSimilarity.Tracial.GeneratedGNSRecovery

namespace OAI

/-! Operator transfer to the constructed generated algebra. These results
use the exact factor embeddings of the canonical model. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A R P : Type*} [CStarAlgebra A] [CStarAlgebra R] [CStarAlgebra P]
  [PartialOrder P] [StarOrderedRing P]
  (τ : P →ₚ[ℂ] ℂ) (htr : ∀ a b : P, τ (a * b) = τ (b * a))
  (φ : A →⋆ₐ[ℂ] P) (ψ : R →⋆ₐ[ℂ] P)

def canonicalGeneratedOperator (S : τ.GNS →L[ℂ] τ.GNS) :=
  generatedGNSCompression τ (canonicalGeneratedAlgebra τ htr φ ψ) S

theorem canonicalGeneratedOperator_commutes
    (S : τ.GNS →L[ℂ] τ.GNS)
    (hcomm : ∀ r, S.comp (τ.gnsStarAlgHom (ψ r)) =
      (τ.gnsStarAlgHom (ψ r)).comp S) :
    ∀ a : (canonicalGeneratedSecond τ htr φ ψ).range,
      (canonicalGeneratedOperator τ htr φ ψ S).comp
        ((canonicalGeneratedGeometry τ htr φ ψ).left (a : _)) =
      ((canonicalGeneratedGeometry τ htr φ ψ).left (a : _)).comp
        (canonicalGeneratedOperator τ htr φ ψ S) := by
  have h := generatedGNSCompression_commutes τ (canonicalGeneratedAlgebra τ htr φ ψ)
    ψ.range S (fun r => by
      obtain ⟨x, hx⟩ := r.property
      rw [← hx]
      exact hcomm x)
  intro a
  have ha : ((a : canonicalGeneratedAlgebra τ htr φ ψ) : P) ∈ ψ.range := by
    obtain ⟨r, hr⟩ := a.property
    exact ⟨r, congrArg (fun x : canonicalGeneratedAlgebra τ htr φ ψ => (x : P)) hr⟩
  exact h ⟨(a : canonicalGeneratedAlgebra τ htr φ ψ), ha⟩

theorem canonicalGeneratedOperator_traceCornerBound
    (S : τ.GNS →L[ℂ] τ.GNS) {t ε : ℝ}
    (hbound : (gnsTracialGeometry τ htr).TraceCornerBound ψ.range S t ε) :
    (canonicalGeneratedGeometry τ htr φ ψ).TraceCornerBound
      (canonicalGeneratedSecond τ htr φ ψ).range
      (canonicalGeneratedOperator τ htr φ ψ S) t ε := by
  change (canonicalGeneratedGeometry τ htr φ ψ).TraceCornerBound
    (ψ.codRestrict (canonicalGeneratedAlgebra τ htr φ ψ)
      (canonicalGenerated_second_mem τ htr φ ψ)).range _ t ε
  rw [range_codRestrict_eq_comap]
  exact generatedGNSCompression_traceCornerBound τ
    (canonicalGeneratedAlgebra τ htr φ ψ) htr ψ.range S hbound

variable [PartialOrder A] [StarOrderedRing A]
  (τA : A →ₚ[ℂ] ℂ) (hφ : ∀ a, τ (φ a) = τA a)

/-- Recovery in the constructed generated model has no density or
generated-algebra hypothesis left to supply. -/
theorem norm_commutator_le_canonicalGeneratedOperator
    (T : τA.GNS →L[ℂ] τA.GNS) (S : τ.GNS →L[ℂ] τ.GNS)
    (hT : (gnsTracialHomIsometry τA τ φ hφ).toContinuousLinearMap.adjoint.comp
      (S.comp (gnsTracialHomIsometry τA τ φ hφ).toContinuousLinearMap) = T)
    (a : A) :
    ‖commutator T (τA.gnsStarAlgHom a)‖ ≤
      ‖(canonicalGeneratedGeometry τ htr φ ψ).baseOperator
        (canonicalGeneratedFirst τ htr φ ψ).range
        (commutator (canonicalGeneratedOperator τ htr φ ψ S)
          ((canonicalGeneratedGeometry τ htr φ ψ).left
            (canonicalGeneratedFirst τ htr φ ψ a)))‖ :=
  norm_commutator_le_generated_GNS_compression τA τ
    (canonicalGeneratedAlgebra τ htr φ ψ) φ (canonicalGenerated_first_mem τ htr φ ψ)
    hφ htr T S hT a

end KadisonSimilarity

end

end OAI
