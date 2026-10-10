import OAI.Analysis.KadisonSimilarity.Tracial.ConstantMomentLimit
import OAI.Analysis.KadisonSimilarity.Tracial.ConjugateMomentCriterion
import OAI.Analysis.KadisonSimilarity.FreeProduct.ScalarFreeMonotone
import OAI.Analysis.KadisonSimilarity.Tracial.PopaConjugatePosition
import OAI.Analysis.KadisonSimilarity.Tracial.SourceUltrapowerInclusion

namespace OAI

/-! Source quotient unitaries and the concrete conjugated constant embedding. -/

noncomputable section
namespace KadisonSimilarity
open HochschildPatching HochschildUltrapower
open scoped ComplexOrder BoundedContinuousFunction

section Moments
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
  (tr : ∀ a b, τ (a * b) = τ (b * a))

theorem ConstantIntegerMoments.scalarFree (u : ℕ → unitary B)
    (hu : ConstantIntegerMoments τ h1 ω tr u) :
    ScalarFree (quotientTrace τ h1 ω tr).toLinearMap (constant τ h1 ω tr).range
      (((Unitary.conjStarAlgAut ℂ (Ultrapower τ h1 ω tr)
        (quotientUnitary τ h1 ω tr u)).toStarAlgHom).comp (constant τ h1 ω tr)).range := by
  apply scalarFree_conjugate_of_integer_moments
    (quotientTrace τ h1 ω tr).toLinearMap (quotientTrace_one τ h1 ω tr)
    (quotientTrace_tracial τ h1 ω tr) (constant τ h1 ω tr)
    (quotientUnitary τ h1 ω tr u)
  intro a l hl hk
  simpa only [PositiveLinearMap.coe_toLinearMap, quotientTrace_constant] using hu a l hl hk
end Moments

section Inclusion
variable {A B R : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [CStarAlgebra R]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (hA : τA 1 = 1) (hB : τB 1 = 1) (ω : Ultrafilter ℕ)
  (trA : ∀ a b, τA (a * b) = τA (b * a))
  (trB : ∀ a b, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

theorem tracialUltrapowerMap_constant (a : A) :
    tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ (constant τA hA ω trA a) =
      constant τB hB ω trB (φ a) := by
  change quotientHom τB hB ω trB
    (boundedSequenceStarHom φ (constantSequence a)) =
    quotientHom τB hB ω trB (constantSequence (φ a))
  congr 1

theorem conjugatedConstantEmbedding_coordinate (ρ : R →⋆ₐ[ℂ] A)
    (u : ℕ → unitary A) (a : R) :
    conjugatedConstantEmbedding τA τB hA hB ω trA trB φ hφ ρ
      (quotientUnitary τA hA ω trA u) a =
    Unitary.conjStarAlgAut ℂ (Ultrapower τB hB ω trB)
      (quotientUnitary τB hB ω trB (fun n => mapUnitary φ (u n)))
      (constant τB hB ω trB (φ (ρ a))) := by
  change tracialUltrapowerMap τA τB hA hB ω trA trB φ hφ
    ((quotientUnitary τA hA ω trA u : Ultrapower τA hA ω trA) *
      constant τA hA ω trA (ρ a) * star (quotientUnitary τA hA ω trA u : Ultrapower τA hA ω trA)) = _
  rw [map_mul, map_mul, map_star, tracialUltrapowerMap_quotientUnitary,
    tracialUltrapowerMap_constant]
  rfl

/-- Ambient constant freeness supplies the exact published-input proposition,
with the witness retained in the source ultrapower. -/
theorem popaConjugateFreeness_of_constant_moments
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) (ρ : R →⋆ₐ[ℂ] A)
    (u : ℕ → unitary A)
    (hu : ConstantIntegerMoments τB hB ω trB (fun n => mapUnitary φ (u n))) :
    Popa1995ConjugateFreenessInput τA τB hA hB ω trA trB φ hφ hω ρ := by
  refine ⟨quotientUnitary τA hA ω trA u, ?_⟩
  apply (hu.scalarFree τB hB ω trB (fun n => mapUnitary φ (u n))).mono le_rfl
  rintro x ⟨a, rfl⟩
  refine ⟨φ (ρ a), ?_⟩
  exact (conjugatedConstantEmbedding_coordinate τA τB hA hB ω trA trB φ hφ ρ u a).symm
end Inclusion

end KadisonSimilarity

end

end OAI
