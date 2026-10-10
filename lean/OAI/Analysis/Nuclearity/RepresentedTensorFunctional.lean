import OAI.Analysis.Nuclearity.TensorCoefficientFunctional
import OAI.Analysis.OperatorAlgebra.CyclicCoefficientApproximation
import OAI.Analysis.Nuclearity.UnitizedCoefficientMaps

namespace OAI

/-! The finite coefficient functional agrees with the positive tensor
functional of the actual coefficient-enlarged map, on the full completion. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

variable {B C D H I : Type*} [NonUnitalCStarAlgebra B] [CStarAlgebra C]
  [NonUnitalCStarAlgebra D] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] [PartialOrder D] [StarOrderedRing D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

local instance representedTensorOrder : PartialOrder (MinimalTensor B C) := CStarAlgebra.spectralOrder _
local instance representedTensorOrdered : StarOrderedRing (MinimalTensor B C) := CStarAlgebra.spectralOrderedRing _

def representedMap (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : B →L[ℂ] D) :
    B →L[ℂ] (H →L[ℂ] H) := (starHomContinuousLinear π).comp T

lemma representedMap_cp (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : B →L[ℂ] D)
    (hT : CompletelyPositive T) : CompletelyPositive (representedMap π T) := by
  intro n M hM
  have h := map_nonneg (CStarMatrix.mapₙₐ π) (hT n M hM)
  convert h using 1
  ext i j
  rfl

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
  [PartialOrder D] [StarOrderedRing D] in
lemma representedMap_commute (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : B →L[ℂ] D)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c)) :
    ∀ b c, Commute (representedMap π T b) (η c) := fun b c => hc (T b) c

def representedTensorFunctional (hB : Nuclear B) (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (T : B →L[ℂ] D) (hT : CompletelyPositive T)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c)) (ξ : H) :
    MinimalTensor B C →ₚ[ℂ] ℂ :=
  nuclearTensorFunctional hB (representedMap π T) (representedMap_cp π T hT) η
    (representedMap_commute π T η hc) ξ

lemma representedTensorFunctional_elementary (hB : Nuclear B)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : B →L[ℂ] D) (hT : CompletelyPositive T)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c)) (ξ : H)
    (b : B) (c : C) :
    representedTensorFunctional hB π T hT η hc ξ (minimalElementary b c) =
      ⟪ξ, π (T b) (η c ξ)⟫_ℂ := by
  rw [representedTensorFunctional, nuclearTensorFunctional_elementary]
  rfl


lemma representedTensorFunctional_sum (hB : Nuclear B)
    (π : D →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (T : B →L[ℂ] D) (hT : CompletelyPositive T)
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c)) (ξ : H)
    (x : I → B) (y : I → C) :
    representedTensorFunctional hB π T hT η hc ξ (∑ i, minimalElementary (x i) (y i)) =
      ∑ i, ⟪ξ, π (T (x i)) (η (y i) ξ)⟫_ℂ := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact representedTensorFunctional_elementary hB π T hT η hc ξ (x i) (y i)

theorem tensorCoefficientFunctional_unitized (hB : Nuclear B)
    (π : Unitization ℂ D →⋆ₐ[ℂ] (H →L[ℂ] H))
    (η : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ d c, Commute (π d) (η c)) (ξ : H)
    (T W : B →L[ℂ] D) (hT : CompletelyPositive T) (hW : CompletelyPositive W)
    (a : I → Unitization ℂ D) (x : I → B)
    (hWval : ∀ b, W b = unitizedCoefficientEnlargement T a x b) :
    let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ D)
    let hρ := fun (d : D) (c : C) => hc (d : Unitization ℂ D) c
    ∀ z : MinimalTensor B C,
      tensorCoefficientFunctional (representedMap ρ T) η x (fun i => π (a i) ξ) z =
        representedTensorFunctional hB ρ W hW η hρ ξ z := by
  dsimp only
  let ρ := π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ D)
  let hρ : ∀ d c, Commute (ρ d) (η c) := fun d c => hc (d : Unitization ℂ D) c
  let Φ := representedTensorFunctional hB ρ W hW η hρ ξ
  let L : MinimalTensor B C →L[ℂ] ℂ := ⟨Φ.toLinearMap, map_continuous Φ⟩
  have he : tensorCoefficientFunctional (representedMap ρ T) η x (fun i => π (a i) ξ) = L := by
    apply minimalTensor_clm_ext
    intro b c
    rw [tensorCoefficientFunctional_elementary hB _ (representedMap_cp ρ T hT) _
      (representedMap_commute ρ T η hρ)]
    change _ = representedTensorFunctional hB ρ W hW η hρ ξ (minimalElementary b c)
    rw [representedTensorFunctional_elementary, hWval]
    exact (unitized_coefficient_representation π ξ T a x b (η c) (fun d => hc d c)).symm
  intro z
  exact DFunLike.congr_fun he z

end WeakPureInfiniteness

end

end OAI
