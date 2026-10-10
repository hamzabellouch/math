import OAI.Analysis.OperatorAlgebra.TracialMinimalBound
import OAI.Analysis.OperatorAlgebra.TracialTensorCompletion

namespace OAI

/-! Extension of the finite tracial multiplication representation to the actual
minimal tensor product. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

lemma tracialMinimalAlgebraic_mul
    (z w : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    minimalAlgebraicLinear (z * w) =
      minimalAlgebraicLinear z * minimalAlgebraicLinear w := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    induction w using TensorProduct.inductionOn with
    | tmul c d =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, minimalAlgebraicLinear_tmul,
        minimalElementary_mul]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]

lemma tracialMinimalAlgebraic_star
    (z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    minimalAlgebraicLinear (star z) = star (minimalAlgebraicLinear z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    simp only [TensorProduct.star_tmul, minimalAlgebraicLinear_tmul, minimalElementary_star]
  | add x y hx hy => simp only [star_add, map_add, hx, hy]

variable [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
  (τ : Pureness.TracialState M.toStarSubalgebra)
  (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
  (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
  (hEf : ∀ T, T ∈ M → E T = T)

include E hE hEr hEf in
lemma tracialMinimalMultiplication_norm_le
    (z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    ‖tracialMultiplicationTensor M τ z‖ ≤ ‖minimalAlgebraicLinear z‖ := by
  have h₁ := tracial_multiplication_norm_le M τ E hE hEr hEf z
  have h₂ := tracialSpatialTensor_norm_le_minimal M z
  exact h₁.trans h₂

/-- The finite tracial amenability representation, constructed from the
expectation by the existing minimal tensor extension theorem. -/
def tracialMinimalMultiplication :
    MinimalTensor M.toStarSubalgebra M.toStarSubalgebraᵐᵒᵖ →⋆ₙₐ[ℂ]
      (τ.functional.GNS →L[ℂ] τ.functional.GNS) :=
  tracialTensorMinimal τ.functional τ.tracial
    (tracialMinimalMultiplication_norm_le M τ E hE hEr hEf)

lemma tracialMinimalMultiplication_algebraic
    (z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    tracialMinimalMultiplication M τ E hE hEr hEf (minimalAlgebraicLinear z) =
      tracialMultiplicationTensor M τ z :=
  tracialTensorMinimal_algebraic τ.functional τ.tracial
    (tracialMinimalMultiplication_norm_le M τ E hE hEr hEf) z

@[simp] lemma tracialMinimalMultiplication_elementary (a b : M.toStarSubalgebra) :
    tracialMinimalMultiplication M τ E hE hEr hEf
        (minimalElementary a (MulOpposite.op b)) =
      τ.functional.gnsStarAlgHom a *
        NuclearTrace.rightGNS τ.functional τ.tracial (MulOpposite.op b) :=
  tracialTensorMinimal_elementary τ.functional τ.tracial
    (tracialMinimalMultiplication_norm_le M τ E hE hEr hEf) a b

end WeakPureInfiniteness

end

end OAI
