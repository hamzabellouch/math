import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.ASI

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

structure AllFieldWitness (F : Type*) [Field F] where
  rows : ℕ
  inner : ℕ
  columns : ℕ
  multiplicity : ℕ
  rankBound : ℕ
  order : ℕ
  degree : ℕ
  rows_pos : 0 < rows
  inner_pos : 0 < inner
  columns_pos : 0 < columns
  multiplicity_pos : 0 < multiplicity
  rankBound_pos : 0 < rankBound
  approximation : Tensor.PolynomialApproximation
    (Tensor.directSum (fun _ : Fin multiplicity =>
      Tensor.matrixCoefficients (K := F) (Fin rows) (Fin inner) (Fin columns)))
    rankBound order degree

namespace AllFieldWitness

variable {F : Type*} [Field F]

def volume (W : AllFieldWitness F) : ℕ := W.rows * W.inner * W.columns

theorem volume_pos (W : AllFieldWitness F) : 0 < W.volume :=
  Nat.mul_pos (Nat.mul_pos W.rows_pos W.inner_pos) W.columns_pos

theorem finite_inequality (W : AllFieldWitness F) :
    (W.multiplicity : ℝ) * (W.volume : ℝ) ^ (Arithmetic.omega F / 3) ≤ W.rankBound :=
  Arithmetic.equalVolume_inequality_of_polynomialApproximation
    W.rows_pos W.inner_pos W.columns_pos W.approximation

theorem log_inequality (W : AllFieldWitness F) :
    Real.log (W.multiplicity : ℝ) +
      (Arithmetic.omega F / 3) * Real.log (W.volume : ℝ) ≤
        Real.log (W.rankBound : ℝ) := by
  have hm : (0 : ℝ) < W.multiplicity := Nat.cast_pos.mpr W.multiplicity_pos
  have hv : (0 : ℝ) < W.volume := Nat.cast_pos.mpr W.volume_pos
  have hp := Real.rpow_pos_of_pos hv (Arithmetic.omega F / 3)
  have h := Real.log_le_log (mul_pos hm hp) W.finite_inequality
  rw [Real.log_mul hm.ne' hp.ne', Real.log_rpow hv] at h
  exact h

end AllFieldWitness
end MatrixMultiplication

end

end OAI
