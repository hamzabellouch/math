import OAI.Analysis.OperatorAlgebra.HilbertDualOperators
import OAI.Analysis.OperatorAlgebra.HilbertSchmidtUnitaryActions

namespace OAI

/-! The left/right actions used by the finite-density argument are genuine
spatial star representations on the Hilbert–Schmidt completion. -/

noncomputable section
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance densityHSNormed : NormedAddCommGroup (NuclearUltrapower.HilbertSchmidt H) := inferInstance
instance densityHSInner : InnerProductSpace ℂ (NuclearUltrapower.HilbertSchmidt H) := inferInstance
instance densityHSComplete : CompleteSpace (NuclearUltrapower.HilbertSchmidt H) := inferInstance
instance densityHSScalar : NormedSpace ℂ (NuclearUltrapower.HilbertSchmidt H) := inferInstance
instance densityHSBounded : IsBoundedSMul ℂ (NuclearUltrapower.HilbertSchmidt H) :=
  NormedSpace.toIsBoundedSMul
instance densityHSContinuous : ContinuousSMul ℂ (NuclearUltrapower.HilbertSchmidt H) :=
  IsBoundedSMul.continuousSMul

def densityLeftRepresentation : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (NuclearUltrapower.HilbertSchmidt H →L[ℂ] NuclearUltrapower.HilbertSchmidt H) :=
  Pureness.spatialLeftHom (K := StrongDual ℂ H) (StarAlgHom.id ℂ (H →L[ℂ] H))

def densityRightRepresentation : (H →L[ℂ] H)ᵐᵒᵖ →⋆ₐ[ℂ]
    (NuclearUltrapower.HilbertSchmidt H →L[ℂ] NuclearUltrapower.HilbertSchmidt H) :=
  Pureness.spatialRightHom (H := H) hilbertDualRepresentation

lemma densityLeftRight_commute (T S : H →L[ℂ] H) :
    Commute (densityLeftRepresentation T) (densityRightRepresentation (MulOpposite.op S)) := by
  unfold densityLeftRepresentation densityRightRepresentation
  exact Pureness.spatialLeftRight_commute (StarAlgHom.id ℂ (H →L[ℂ] H))
    (hilbertDualRepresentation (H := H)) T (MulOpposite.op S)

lemma densityLeft_coe (T : H →L[ℂ] H) (z : H ⊗[ℂ] StrongDual ℂ H) :
    densityLeftRepresentation T (z : NuclearUltrapower.HilbertSchmidt H) =
      (TensorProduct.mapL T (ContinuousLinearMap.id ℂ (StrongDual ℂ H)) z :
        NuclearUltrapower.HilbertSchmidt H) :=
  UnitalTomsWinter.spatialTensorOp_coe T 1 z

lemma densityLeft_unitary (U : H ≃ₗᵢ[ℂ] H) :
    densityLeftRepresentation (U : H →L[ℂ] H) =
      (hsLeftUnitary U : NuclearUltrapower.HilbertSchmidt H →L[ℂ] NuclearUltrapower.HilbertSchmidt H) := by
  apply UnitalTomsWinter.spatialTensorOp_ext (H := H) (K := StrongDual ℂ H)
  intro x f
  change UnitalTomsWinter.spatialTensorOp (U : H →L[ℂ] H) 1
    ((x ⊗ₜ[ℂ] f : H ⊗[ℂ] StrongDual ℂ H) : NuclearUltrapower.HilbertSchmidt H) = _
  rw [UnitalTomsWinter.spatialTensorOp_coe]
  change (TensorProduct.mapL (U : H →L[ℂ] H) (1 : StrongDual ℂ H →L[ℂ] StrongDual ℂ H) (x ⊗ₜ[ℂ] f) :
    NuclearUltrapower.HilbertSchmidt H) = hsLeftUnitary U _
  simp only [TensorProduct.mapL_tmul, one_apply_eq_self, hsLeftUnitary,
    NuclearUltrapower.completionUnitary_coe, TensorProduct.congrIsometry_apply,
    TensorProduct.congr_tmul]
  rfl

lemma densityRight_unitary (U : H ≃ₗᵢ[ℂ] H) :
    densityRightRepresentation (MulOpposite.op (U : H →L[ℂ] H)) =
      (hsRightUnitary U : NuclearUltrapower.HilbertSchmidt H →L[ℂ] NuclearUltrapower.HilbertSchmidt H) := by
  apply UnitalTomsWinter.spatialTensorOp_ext (H := H) (K := StrongDual ℂ H)
  intro x f
  change UnitalTomsWinter.spatialTensorOp 1 (hilbertDualOperator (U : H →L[ℂ] H))
    ((x ⊗ₜ[ℂ] f : H ⊗[ℂ] StrongDual ℂ H) : NuclearUltrapower.HilbertSchmidt H) = _
  rw [UnitalTomsWinter.spatialTensorOp_coe]
  change (TensorProduct.mapL (1 : H →L[ℂ] H) (hilbertDualOperator (U : H →L[ℂ] H)) (x ⊗ₜ[ℂ] f) :
    NuclearUltrapower.HilbertSchmidt H) = hsRightUnitary U _
  simp only [TensorProduct.mapL_tmul, one_apply_eq_self, hsRightUnitary,
    NuclearUltrapower.completionUnitary_coe, TensorProduct.congrIsometry_apply,
    TensorProduct.congr_tmul]
  have hf : hilbertDualOperator (U : H →L[ℂ] H) f = NuclearUltrapower.dualUnitary U.symm f := by
    ext y
    rw [hilbertDualOperator_apply, NuclearUltrapower.dualUnitary_apply]
    rfl
  change ((x ⊗ₜ[ℂ] hilbertDualOperator (U : H →L[ℂ] H) f : H ⊗[ℂ] StrongDual ℂ H) :
    NuclearUltrapower.HilbertSchmidt H) = (x ⊗ₜ[ℂ] NuclearUltrapower.dualUnitary U.symm f)
  rw [hf]

end WeakPureInfiniteness

end

end OAI
