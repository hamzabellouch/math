import OAI.Analysis.Nuclearity.MinimalTensorFactorRestrictions
import OAI.Analysis.Nuclearity.RepresentedAlgebra
import OAI.Analysis.Nuclearity.FactorTensorExtension

namespace OAI

/-! Algebraic faithfulness of the two represented image algebras, for the
actual irreducible representation in the ideal-separation argument. -/

noncomputable section
open KirchbergRordam.GenericRW
open scoped TensorProduct

namespace WeakPureInfiniteness

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance representedFactorUnital : CStarAlgebra (MinimalTensor A B) :=
  minimalTensorUnitalStructure A B

def leftRepresentedMap (π : MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H)) :=
  π.comp (UnitalMinimalTensor.leftEmbedding A B)

def rightRepresentedMap (π : MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H)) :=
  π.comp (UnitalMinimalTensor.rightEmbedding A B)

theorem representedFactor_commute (π : MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (a : representedAlgebra (leftRepresentedMap π))
    (b : representedAlgebra (rightRepresentedMap π)) :
    Commute (representedInclusion _ a) (representedInclusion _ b) := by
  rcases a.property with ⟨x, hx⟩
  rcases b.property with ⟨y, hy⟩
  change Commute a.val b.val
  rw [← hx, ← hy]
  exact (UnitalMinimalTensor.legs_commute A B x y).map π

theorem representedFactor_tensor_injective
    (π : MinimalTensor A B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hs : ∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ z : ℂ, T = z • 1) :
    Function.Injective (Pureness.commutingStarTensorHom
      (representedInclusion (leftRepresentedMap π))
      (representedInclusion (rightRepresentedMap π)) (representedFactor_commute π)) := by
  let M := GroupedFactors.bicommutant (leftRepresentedMap π).range
  apply factor_starTensor_injective M (minimalTensor_left_factor π hs)
    (representedInclusion _) (representedInclusion _)
    (representedInclusion_injective _) (representedInclusion_injective _)
  · intro a
    exact GroupedFactors.subset_bicommutant (leftRepresentedMap π).range a.val a.property
  · intro b
    rcases b.property with ⟨y, hy⟩
    change b.val ∈ M.commutant
    rw [← hy]
    exact minimalTensor_right_mem_left_commutant π y

end WeakPureInfiniteness

end

end OAI
