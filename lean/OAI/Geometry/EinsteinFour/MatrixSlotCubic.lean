import OAI.Geometry.EinsteinFour.MatrixSlotOperator

namespace OAI

/-! The varying matrix-slot correction is the actual cubic trace in the
weighted Hessian identity. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Angular Matrix

noncomputable section

theorem matrixPairing_eq_trace (A B : Mat) :
    matrixPairing A B = Matrix.trace (A * Bᵀ) := by
  simp only [matrixPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]

theorem matrixSlotAction_eq (A M : Mat) :
    matrixSlotAction A M = (1 / 2 : ℝ) • (A * M + M * A) -
      (Matrix.trace (A * M) / 3) • (1 : Mat) := by
  ext a b
  simp only [matrixSlotAction, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

theorem matrixSlotAction_self_pairing (A M : Mat)
    (hs : symmetric M) (ht : traceFree M) :
    matrixPairing (matrixSlotAction A M) M = Matrix.trace (A * (M * M)) := by
  have hm : Mᵀ = M := by ext a b; exact hs b a
  have htr : Matrix.trace M = 0 := ht
  rw [matrixPairing_eq_trace, hm, matrixSlotAction_eq,
    Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_smul, htr, smul_zero, sub_zero,
    Matrix.mul_assoc M A M, Matrix.trace_mul_comm M (A * M), Matrix.mul_assoc]
  simp only [smul_eq_mul]
  ring

/-- Summing over the derivative index gives the cubic trace, with no
diagonalization assumption on the varying coefficient. -/
theorem matrixSlot_cubic_trace (A : Mat) (Z : Gradient)
    (hs : ∀ j, symmetric (Z j)) (ht : ∀ j, traceFree (Z j)) :
    inner ℝ (matrixSlotOperator A (gradientVector Z)) (gradientVector Z) =
      Matrix.trace (A * (∑ j, Z j * Z j)) := by
  have hslot (j : Fin 4) (a b : Fin 3) :
      matrixSlotOperator A (gradientVector Z) (j, a, b) =
        matrixSlotAction A (Z j) a b :=
    matrixSlotOperator_on_traceFree A (gradientVector Z) ht j a b
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_prod_type]
  change (∑ j, ∑ a, ∑ b,
    Z j a b * matrixSlotOperator A (gradientVector Z) (j, a, b)) = _
  calc
    _ = ∑ j, matrixPairing (matrixSlotAction A (Z j)) (Z j) := by
      simp only [matrixPairing, hslot, mul_comm]
    _ = ∑ j, Matrix.trace (A * (Z j * Z j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact matrixSlotAction_self_pairing A (Z j) (hs j) (ht j)
    _ = _ := by rw [Matrix.mul_sum, Matrix.trace_sum]

end
end PositiveEinsteinFour.Geometry

end OAI
