import OAI.Analysis.Nuclearity.NuclearCommutingCP
import OAI.Analysis.WeakInfiniteness.CentralState

namespace OAI

/-! The positive tensor functional of KR02 (7.14). It is obtained from the
actual completely positive map and a commuting representation, using
nuclearity for continuity in the minimal tensor norm. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

variable {B C H : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance tensorFunctionalOrder : PartialOrder (MinimalTensor B C) := CStarAlgebra.spectralOrder _
local instance tensorFunctionalOrdered : StarOrderedRing (MinimalTensor B C) := CStarAlgebra.spectralOrderedRing _

def nuclearTensorFunctional (hB : Nuclear B)
    (f : B →L[ℂ] (H →L[ℂ] H)) (hf : CompletelyPositive f)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ b c, Commute (f b) (η c)) (ξ : H) :
    MinimalTensor B C →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((vectorStateContinuous (NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H)) ξ).toLinearMap.comp
      (cpCommutingPositiveMap hB f hf η hc).toLinearMap)
    (fun _ hx => map_nonneg
      (vectorStateContinuous_cp (NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H)) ξ).toMap
      (map_nonneg (cpCommutingPositiveMap hB f hf η hc) hx))

lemma nuclearTensorFunctional_elementary (hB : Nuclear B)
    (f : B →L[ℂ] (H →L[ℂ] H)) (hf : CompletelyPositive f)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ b c, Commute (f b) (η c))
    (ξ : H) (b : B) (c : C) :
    nuclearTensorFunctional hB f hf η hc ξ (minimalElementary b c) =
      ⟪ξ, f b (η c ξ)⟫_ℂ := by
  change ⟪ξ, cpCommutingLinear f η (minimalElementary b c) ξ⟫_ℂ = _
  rw [cpCommutingLinear_elementary hB f hf η hc]
  rfl

end WeakPureInfiniteness

end

end OAI
