import OAI.Analysis.OperatorAlgebra.TracialMinimalMultiplication

namespace OAI

/-! The minimal tensor norm bound for multiplication associated with a
finite-tracial representation carrying a completely positive expectation. -/
noncomputable section
open scoped TensorProduct ComplexOrder
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tracialMinimalMultiplication_bound_of_expectation (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (h : ∃ E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H),
      CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ M) ∧ (∀ T, T ∈ M → E T = T)) :
    ∀ z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ,
      ‖tracialMultiplicationTensor M τ z‖ ≤ ‖minimalAlgebraicLinear z‖ := by
  obtain ⟨E, hE, _hn, hr, hf⟩ := h
  exact tracialMinimalMultiplication_norm_le M τ E hE hr hf

end WeakPureInfiniteness

end

end OAI
