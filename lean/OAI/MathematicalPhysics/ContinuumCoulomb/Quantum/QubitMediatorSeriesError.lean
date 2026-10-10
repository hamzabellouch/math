import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorSeriesMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorNorm

namespace OAI

/-! The common low Hamiltonian contributes only a decreasing residual
to the exact third-order compression. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]

theorem qmaSandwich_operator_norm (P L : Matrix σ σ ℂ) :
    ‖spinMatrixOperator (P*L*P)‖ ≤ ‖spinMatrixOperator P‖^2*‖spinMatrixOperator L‖ := by
  rw [spinMatrixOperator_mul,spinMatrixOperator_mul]
  calc
    _ ≤ ‖(spinMatrixOperator P).comp (spinMatrixOperator L)‖*‖spinMatrixOperator P‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖spinMatrixOperator P‖*‖spinMatrixOperator L‖)*‖spinMatrixOperator P‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by ring

theorem qmaThirdResidual_norm (L : Matrix σ σ ℂ) (P : κ → Matrix σ σ ℂ)
    (r : ℝ) (hr : 0 < r) :
    ‖spinMatrixOperator (((r:ℂ)⁻¹)^2 • (∑ e, P e*L*P e))‖ ≤
      r⁻¹^2*((∑ e, ‖spinMatrixOperator (P e)‖^2)*‖spinMatrixOperator L‖) := by
  rw [spinMatrixOperator_smul,norm_smul,norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hr,spinMatrixOperator_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    _ ≤ ∑ e, ‖spinMatrixOperator (P e*L*P e)‖ := norm_sum_le _ _
    _ ≤ ∑ e, ‖spinMatrixOperator (P e)‖^2*‖spinMatrixOperator L‖ :=
      Finset.sum_le_sum (fun e _ => qmaSandwich_operator_norm _ _)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem qmaThirdResidual_polynomial_bound (L : Matrix σ σ ℂ) (P : κ → Matrix σ σ ℂ)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hP : ∑ e, ‖spinMatrixOperator (P e)‖^2 ≤ K) (hL : ‖spinMatrixOperator L‖ ≤ K*r) :
    ‖spinMatrixOperator (((r:ℂ)⁻¹)^2 • (∑ e, P e*L*P e))‖ ≤ K^2/r := by
  calc
    _ ≤ r⁻¹^2*((∑ e, ‖spinMatrixOperator (P e)‖^2)*‖spinMatrixOperator L‖) :=
      qmaThirdResidual_norm L P r hr
    _ ≤ r⁻¹^2*(K*(K*r)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hP hL (norm_nonneg _) hK) (sq_nonneg _)
    _ = _ := by field_simp

end ContinuumCoulomb

end

end OAI
