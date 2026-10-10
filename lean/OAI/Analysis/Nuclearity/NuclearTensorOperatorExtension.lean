import OAI.Analysis.OperatorAlgebra.HilbertOperatorExtension
import OAI.Analysis.Nuclearity.UnitalNuclearTensor

namespace OAI

/-! Extension of a nuclear commuting tensor representation to all operators
in its right factor. This is the concrete extension in the commutant
injectivity argument. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder
namespace WeakPureInfiniteness

local instance tensorOperatorExtensionUnital {B C : Type*}
    [CStarAlgebra B] [CStarAlgebra C] : CStarAlgebra (MinimalTensor B C) :=
  minimalTensorUnitalStructure B C

variable {A C H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

/-- The extension is cpc and agrees with the product on the original commuting
representations. It is not asserted to be multiplicative on the larger algebra. -/
theorem nuclear_commuting_operator_extension (hA : Nuclear A)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (η : C →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hη : Function.Injective η) (hc : ∀ a c, Commute (π a) (η c)) :
    letI : PartialOrder (MinimalTensor A (H →L[ℂ] H)) := CStarAlgebra.spectralOrder _
    letI : StarOrderedRing (MinimalTensor A (H →L[ℂ] H)) := CStarAlgebra.spectralOrderedRing _
    ∃ Φ : MinimalTensor A (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H),
      CompletelyPositive Φ ∧ ‖Φ‖ ≤ 1 ∧
      ∀ a c, Φ (minimalElementary a (η c)) = π a * η c := by
  let : PartialOrder (MinimalTensor A C) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (MinimalTensor A C) := CStarAlgebra.spectralOrderedRing _
  let : PartialOrder (MinimalTensor A (H →L[ℂ] H)) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (MinimalTensor A (H →L[ℂ] H)) := CStarAlgebra.spectralOrderedRing _
  let m := unitalNuclearCommuting hA π η hc
  let j := unitalTensorInclusion (A := A) η
  let mL := starHomContinuousLinear m.toNonUnitalStarAlgHom
  obtain ⟨Φ, hΦ, hΦn, he⟩ := hilbertOperator_cpc_extension j
    (unitalTensorInclusion_injective η hη) mL
    (starHomContinuous_completelyPositive _) (starHomContinuousLinear_norm_le_one _)
  refine ⟨Φ, hΦ, hΦn, ?_⟩
  intro a c
  have hh := he (minimalElementary a c)
  change Φ (unitalTensorInclusion η (minimalElementary a c)) =
    unitalNuclearCommuting hA π η hc (minimalElementary a c) at hh
  simpa only [unitalTensorInclusion_elementary, unitalNuclearCommuting_elementary] using hh

end WeakPureInfiniteness

end

end OAI
