import OAI.Analysis.OperatorAlgebra.TracialExpectationBound
import OAI.Analysis.OperatorAlgebra.TracialTensorFiniteSum

namespace OAI

/-! The finite-tracial bound in the bundled GNS form needed by the actual
corner inclusions. All conversion of GNS structures is done abstractly. -/
noncomputable section
open scoped TensorProduct ComplexOrder
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tracialBundledFiniteProduct_norm_le (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (h : ∃ E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H),
      CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ M) ∧ (∀ T, T ∈ M → E T = T))
    {I : Type*} [Fintype I] (a b : I → M.toStarSubalgebra) :
    ‖∑ i, gnsBundledLeft τ.functional (a i) *
      gnsBundledRight τ.functional τ.tracial (b i)‖ ≤
    ‖∑ i, minimalElementary (a i) (MulOpposite.op (b i))‖ := by
  have hb := tracialMinimalMultiplication_bound_of_expectation M τ h
    (∑ i, a i ⊗ₜ[ℂ] MulOpposite.op (b i))
  change ‖traceTensor τ.functional τ.tracial
    (∑ i, a i ⊗ₜ[ℂ] MulOpposite.op (b i))‖ ≤ _ at hb
  rw [norm_traceTensor_sum] at hb
  simpa only [map_sum, minimalAlgebraicLinear_tmul] using hb

end WeakPureInfiniteness

end

end OAI
