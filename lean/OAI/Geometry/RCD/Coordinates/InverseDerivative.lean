import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Inverse-transpose differentiation and contraction

The metric iteration uses cancellation before estimating the derivative of
an inverse transpose.  These identities work with bounded operators on any
real Hilbert space; no matrix coordinates or condition-number bounds enter
the cancellation itself.
-/

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

namespace RegularPointCoordinates

variable {E X : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The adjoint of the inverse of a bounded linear equivalence. -/
def inverseTranspose (J : E ≃L[ℝ] E) : E →L[ℝ] E :=
  (J.symm : E →L[ℝ] E).adjoint

/-- The inverse transpose cancels the undifferentiated Jacobian in an inner product. -/
theorem inner_apply_inverseTranspose (J : E ≃L[ℝ] E) (ξ w : E) :
    ⟪J ξ, inverseTranspose J w⟫_ℝ = ⟪ξ, w⟫_ℝ := by
  rw [inverseTranspose, adjoint_inner_right]
  simp

/-- The first variation of an inverse transpose. -/
def inverseTransposeVariation (J : E ≃L[ℝ] E) (dJ : E →L[ℝ] E) : E →L[ℝ] E :=
  -(inverseTranspose J ∘L dJ.adjoint ∘L inverseTranspose J)

/-- Exact cancellation in the differentiated inverse-transpose term.
This is the operator form of `re:inverse-transpose-contraction`. -/
theorem inner_apply_inverseTransposeVariation (J : E ≃L[ℝ] E)
    (dJ : E →L[ℝ] E) (ξ w : E) :
    ⟪J ξ, inverseTransposeVariation J dJ w⟫_ℝ =
      -⟪dJ ξ, inverseTranspose J w⟫_ℝ := by
  simp only [inverseTransposeVariation, neg_apply, comp_apply, inner_neg_right]
  rw [inner_apply_inverseTranspose, adjoint_inner_right]

/-- The differentiated-inverse error is controlled by the diagonal
Jacobian derivative, with no operator norm of that derivative. -/
theorem abs_inner_apply_inverseTransposeVariation_le (J : E ≃L[ℝ] E)
    (dJ : E →L[ℝ] E) (ξ w : E) :
    |⟪J ξ, inverseTransposeVariation J dJ w⟫_ℝ| ≤
      ‖dJ ξ‖ * ‖inverseTranspose J w‖ := by
  rw [inner_apply_inverseTransposeVariation, abs_neg]
  exact abs_real_inner_le_norm _ _

/-- The exact metric increment splits into the principal term, the
diagonal differentiated-inverse error, and the squared increment. -/
theorem norm_sq_inverseTranspose_increment (J : E ≃L[ℝ] E)
    (dJ : E →L[ℝ] E) (ξ dv v : E) :
    ‖J ξ + (inverseTranspose J dv + inverseTransposeVariation J dJ v)‖ ^ 2 -
        ‖J ξ‖ ^ 2 =
      2 * ⟪ξ, dv⟫_ℝ - 2 * ⟪dJ ξ, inverseTranspose J v⟫_ℝ +
        ‖inverseTranspose J dv + inverseTransposeVariation J dJ v‖ ^ 2 := by
  rw [norm_add_sq_real, inner_add_right, inner_apply_inverseTranspose,
    inner_apply_inverseTransposeVariation]
  ring

/-- Fréchet derivative of inversion at a bounded linear equivalence. -/
theorem hasFDerivAt_operator_inverse (J : E ≃L[ℝ] E) :
    HasFDerivAt (Ring.inverse : (E →L[ℝ] E) → E →L[ℝ] E)
      (-mulLeftRight ℝ (E →L[ℝ] E) (J.symm : E →L[ℝ] E)
        (J.symm : E →L[ℝ] E)) (J : E →L[ℝ] E) := by
  exact hasFDerivAt_ringInverse J.toUnit

/-- The adjoint operation, viewed as a real continuous linear map. -/
def adjointOperator : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).toContinuousLinearEquiv).toContinuousLinearMap

/-- The inverse-transpose operation on all bounded operators.  Only its
behavior at an invertible operator is used. -/
def operatorInverseTranspose (J : E →L[ℝ] E) : E →L[ℝ] E :=
  (Ring.inverse J).adjoint

@[simp] theorem operatorInverseTranspose_equiv (J : E ≃L[ℝ] E) :
    operatorInverseTranspose (J : E →L[ℝ] E) = inverseTranspose J := by
  change (Ring.inverse (J.toUnit : E →L[ℝ] E)).adjoint = _
  rw [Ring.inverse_unit]
  rfl

/-- Differentiating the inverse transpose of a varying Jacobian. -/
theorem hasFDerivAt_operator_inverseTranspose (J : E ≃L[ℝ] E) :
    HasFDerivAt (operatorInverseTranspose : (E →L[ℝ] E) → E →L[ℝ] E)
      (adjointOperator ∘L
        (-mulLeftRight ℝ (E →L[ℝ] E) (J.symm : E →L[ℝ] E)
          (J.symm : E →L[ℝ] E))) (J : E →L[ℝ] E) := by
  exact adjointOperator.hasFDerivAt.comp _ (hasFDerivAt_operator_inverse J)

/-- The derivative above is exactly the inverse-transpose variation. -/
theorem inverseTranspose_derivative_apply (J : E ≃L[ℝ] E) (dJ : E →L[ℝ] E) :
    (adjointOperator ∘L
      (-mulLeftRight ℝ (E →L[ℝ] E) (J.symm : E →L[ℝ] E)
        (J.symm : E →L[ℝ] E))) dJ = inverseTransposeVariation J dJ := by
  simp [adjointOperator, inverseTransposeVariation, inverseTranspose,
    mulLeftRight_apply, mul_def, comp_assoc]

/-- The cancellation for the actual directional Fréchet derivative of
a variable inverse transpose. -/
theorem inverseTranspose_fderiv_contraction
    {J : X → E →L[ℝ] E} {J' : X →L[ℝ] (E →L[ℝ] E)} {x : X}
    (e : E ≃L[ℝ] E) (he : J x = (e : E →L[ℝ] E))
    (hJ : HasFDerivAt J J' x) (u : X) (ξ w : E) :
    ⟪e ξ, (fderiv ℝ (fun y => operatorInverseTranspose (J y)) x u) w⟫_ℝ =
      -⟪J' u ξ, inverseTranspose e w⟫_ℝ := by
  have hi := hasFDerivAt_operator_inverseTranspose e
  rw [← he] at hi
  have hd := (hi.comp x hJ).fderiv
  change fderiv ℝ (fun y => operatorInverseTranspose (J y)) x = _ at hd
  rw [hd, comp_apply, inverseTranspose_derivative_apply]
  exact inner_apply_inverseTransposeVariation e (J' u) ξ w

/-- The same diagonal bound for the actual directional derivative. -/
theorem abs_inverseTranspose_fderiv_contraction_le
    {J : X → E →L[ℝ] E} {J' : X →L[ℝ] (E →L[ℝ] E)} {x : X}
    (e : E ≃L[ℝ] E) (he : J x = (e : E →L[ℝ] E))
    (hJ : HasFDerivAt J J' x) (u : X) (ξ w : E) :
    |⟪e ξ, (fderiv ℝ (fun y => operatorInverseTranspose (J y)) x u) w⟫_ℝ| ≤
      ‖J' u ξ‖ * ‖inverseTranspose e w‖ := by
  rw [inverseTranspose_fderiv_contraction e he hJ, abs_neg]
  exact abs_real_inner_le_norm _ _

end RegularPointCoordinates

end

end OAI
