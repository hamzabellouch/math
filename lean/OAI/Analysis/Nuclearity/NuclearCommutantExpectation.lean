import OAI.Analysis.Nuclearity.NuclearTensorOperatorExtension
import OAI.Analysis.Nuclearity.CPRepresentationDomain
import OAI.Analysis.OperatorAlgebra.FunctionalCommutant

namespace OAI

/-! A nuclear algebra in any Hilbert-space representation has a cpc projection
onto its commutant. This is the forward, commutant part of Lance's injectivity
argument: extend the commuting tensor representation and use its multiplicative
domain. No converse from injectivity to nuclearity is asserted here. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace WeakPureInfiniteness

local instance commutantExpectationTensorUnital {B C : Type*}
    [CStarAlgebra B] [CStarAlgebra C] : CStarAlgebra (MinimalTensor B C) :=
  minimalTensorUnitalStructure B C

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

/-- A cpc retraction of all bounded operators onto the commutant of any
representation of a nuclear C*-algebra. -/
theorem nuclear_representation_commutant_expectation (hA : Nuclear A)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ P : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H), CompletelyPositive P ∧ ‖P‖ ≤ 1 ∧
      (∀ T, P T ∈ representationCommutant π) ∧
      (∀ T, T ∈ representationCommutant π → P T = T) := by
  let C := representationCommutant π
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let : PartialOrder (MinimalTensor A (H →L[ℂ] H)) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (MinimalTensor A (H →L[ℂ] H)) := CStarAlgebra.spectralOrderedRing _
  let η : C →⋆ₐ[ℂ] (H →L[ℂ] H) := (representationCommutant π).subtype
  obtain ⟨Φ, hΦ, hΦn, he⟩ := nuclear_commuting_operator_extension hA π η
    Subtype.val_injective (representationCommutant_commute π)
  let l := UnitalMinimalTensor.leftEmbedding A (H →L[ℂ] H)
  let r := UnitalMinimalTensor.rightEmbedding A (H →L[ℂ] H)
  have hl (a : A) : Φ (l a) = π a := by
    change Φ (minimalElementary a 1) = π a
    have hh := he a 1
    simpa only [map_one, mul_one] using hh
  let P := Φ.comp (starHomContinuousLinear r.toNonUnitalStarAlgHom)
  refine ⟨P, completelyPositive_comp _ _ (starHomContinuous_completelyPositive _) hΦ,
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hΦn (starHomContinuousLinear_norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)), ?_, ?_⟩
  · intro T
    apply mem_representationCommutant π
    intro a
    exact (cp_extension_commutes l π Φ hΦ hl (r T)
      (fun b => UnitalMinimalTensor.legs_commute A (H →L[ℂ] H) b T) a).symm
  · intro T hT
    change Φ (minimalElementary 1 T) = T
    have hh := he 1 (⟨T, hT⟩ : C)
    change Φ (minimalElementary 1 T) = π 1 * T at hh
    simpa only [map_one, one_mul] using hh

end WeakPureInfiniteness

end

end OAI
