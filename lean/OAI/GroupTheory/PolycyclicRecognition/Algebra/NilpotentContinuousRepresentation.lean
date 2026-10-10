import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAlgebraRepresentation

namespace OAI

/-! # The continuous exponential formula needed for representation descent -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

theorem NilpotentLieModel.exists_continuous_algebra_representation
    {L A : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (N : NilpotentLieModel L) (hn : LieRing.IsNilpotent L) (j : L →ₗ⁅ℝ⁆ A)
    (ExpN : GroupLieAlgebra (𝓘(ℝ,N.modelSpace)) N.carrier → N.carrier)
    (hExpN : IsGroupExponential ExpN) :
    ∃ ρ : N.carrier →* Aˣ, Continuous ρ ∧
      ∀ x : L, ρ (ExpN (N.equiv x)) = algebraExpUnit (j x) := by
  obtain ⟨ρ,hρ,he⟩ := N.exists_algebra_representation hn j
  exact ⟨ρ,hρ.continuous,he ExpN hExpN⟩

end PolycyclicRecognition

end

end OAI
