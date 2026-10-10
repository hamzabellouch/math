import OAI.Analysis.OperatorAlgebra.TracialSpatialMultiplication
import OAI.Analysis.Nuclearity.MinimalTensorExtension

namespace OAI

/-! The finite tracial multiplication representation satisfies the actual
minimal tensor norm bound. This uses its concrete spatial norm and the
preceding cyclic-state argument, without assuming nuclearity of the algebra. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

lemma tracialSpatialTensor_completed_tmul (a : M.toStarSubalgebra)
    (b : M.toStarSubalgebraᵐᵒᵖ) :
    tracialSpatialTensor M (a ⊗ₜ[ℂ] b) =
      (TensorProduct.mapL (a : H →L[ℂ] H)
        ((hilbertDualRepresentation.comp (subalgebraOppositeHom M.toStarSubalgebra)) b)).completion := by
  change UnitalTomsWinter.spatialTensorOp (a : H →L[ℂ] H) 1 *
    UnitalTomsWinter.spatialTensorOp 1
      ((hilbertDualRepresentation.comp (subalgebraOppositeHom M.toStarSubalgebra)) b) = _
  rw [← UnitalTomsWinter.spatialTensorOp_mul, mul_one, one_mul]
  rfl

lemma tracialSpatialTensor_sum_norm_le_minimal {I : Type*} (s : Finset I)
    (a : I → M.toStarSubalgebra) (b : I → M.toStarSubalgebraᵐᵒᵖ) :
    ‖tracialSpatialTensor M (∑ i ∈ s, a i ⊗ₜ[ℂ] b i)‖ ≤
      ‖(∑ i ∈ s, minimalElementary (a i) (b i) :
        MinimalTensor M.toStarSubalgebra M.toStarSubalgebraᵐᵒᵖ)‖ := by
  rw [map_sum]
  simp only [tracialSpatialTensor_completed_tmul]
  exact norm_completed_tensor_sum_le_minimal s a b
    M.toStarSubalgebra.subtype.toNonUnitalStarAlgHom
    (hilbertDualRepresentation.comp (subalgebraOppositeHom M.toStarSubalgebra)).toNonUnitalStarAlgHom

lemma tracialSpatialTensor_norm_le_minimal
    (z : M.toStarSubalgebra ⊗[ℂ] M.toStarSubalgebraᵐᵒᵖ) :
    ‖tracialSpatialTensor M z‖ ≤
      ‖minimalAlgebraicLinear z‖ :=
  algebraic_linear_norm_le (A := M.toStarSubalgebra) (B := M.toStarSubalgebraᵐᵒᵖ)
    (tracialSpatialTensor M).toLinearMap
    (fun _ a b => tracialSpatialTensor_sum_norm_le_minimal M Finset.univ a b) z

end WeakPureInfiniteness

end

end OAI
