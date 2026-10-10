import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorScale
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorCoefficientBounds

namespace OAI

/-! Polynomial norm budget for the exact calibrated effective matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensorEncoding_norm (n : ℕ) : ‖qmaMatrixOperator (qmaFourTensorEncoding n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [one_mul]
  exact le_of_eq (qmaFourTensor_inclusion_norm n p)

theorem qmaFourTensor_column_operator_norm (V : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    ‖qmaMatrixOperator (V*qmaFourTensorEncoding n)‖ ≤ ‖spinMatrixOperator V‖ := by
  rw [qmaMatrixOperator_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (qmaFourTensorEncoding_norm n) (norm_nonneg _)).trans_eq (mul_one _))

theorem qmaFourTensor_compression_norm (C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    ‖spinMatrixOperator ((qmaFourTensorEncoding n).conjTranspose*C*qmaFourTensorEncoding n)‖ ≤
      ‖spinMatrixOperator C‖ := by
  rw [← qmaMatrixOperator_square,qmaMatrixOperator_mul,qmaMatrixOperator_mul,qmaMatrixOperator_star]
  have hE := qmaFourTensorEncoding_norm n
  have hEs : ‖(qmaMatrixOperator (qmaFourTensorEncoding n)).adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hE
  calc
    _ ≤ (‖(qmaMatrixOperator (qmaFourTensorEncoding n)).adjoint‖*‖qmaMatrixOperator C‖)*
        ‖qmaMatrixOperator (qmaFourTensorEncoding n)‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1*‖qmaMatrixOperator C‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hEs (norm_nonneg _)) hE (norm_nonneg _) (by positivity)
    _ = _ := by rw [one_mul,mul_one]; rfl

theorem qmaFourTensorEffectiveMatrix_norm (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤
      ‖spinMatrixOperator C‖+‖spinMatrixOperator V‖^2/8 := by
  have hgram : ‖spinMatrixOperator ((V*qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n))‖ ≤
      ‖spinMatrixOperator V‖^2 := by
    rw [← qmaMatrixOperator_square,qmaMatrixOperator_mul,qmaMatrixOperator_star,
      ContinuousLinearMap.norm_adjoint_comp_self]
    have h := qmaFourTensor_column_operator_norm V
    nlinarith [norm_nonneg (qmaMatrixOperator (V*qmaFourTensorEncoding n)),norm_nonneg (spinMatrixOperator V)]
  rw [qmaFourTensorEffectiveMatrix,spinMatrixOperator_sub]
  apply (norm_sub_le _ _).trans
  rw [spinMatrixOperator_smul,norm_smul]
  have hs : ‖(1/8:ℂ)‖ = (1/8:ℝ) := by norm_num
  rw [hs]
  have hleft := qmaFourTensor_compression_norm C
  nlinarith

def qmaFourTensorNormBudget (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) : ℝ :=
  1+‖spinMatrixOperator V‖+‖spinMatrixOperator C‖+‖spinMatrixOperator V‖^2

theorem qmaFourTensorNormBudget_bounds (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    1 ≤ qmaFourTensorNormBudget V C ∧ ‖spinMatrixOperator V‖ ≤ qmaFourTensorNormBudget V C ∧
      ‖spinMatrixOperator C‖ ≤ qmaFourTensorNormBudget V C ∧
      ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix V C)‖ ≤ qmaFourTensorNormBudget V C := by
  have hv := norm_nonneg (spinMatrixOperator V)
  have hc := norm_nonneg (spinMatrixOperator C)
  have he := qmaFourTensorEffectiveMatrix_norm V C
  unfold qmaFourTensorNormBudget
  constructor
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]
  constructor
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]
  constructor
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]
  · nlinarith [sq_nonneg ‖spinMatrixOperator V‖]

end ContinuumCoulomb

end

end OAI
