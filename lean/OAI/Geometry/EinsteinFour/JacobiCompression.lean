import OAI.Geometry.EinsteinFour.DirichletMatrix
import OAI.Geometry.EinsteinFour.DeterminantCompression
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace OAI

/-! Trace calculations for normalizing the finite Jacobi matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def scalarLift {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ :=
  Matrix.kronecker (1 : NormalMatrix) G

theorem scalarLift_mul {N : ℕ} (G H : Matrix (Fin N) (Fin N) ℝ) :
    scalarLift (G * H) = scalarLift G * scalarLift H := by
  simpa only [scalarLift, Matrix.kronecker, Matrix.one_mul] using
    (Matrix.mul_kronecker_mul (1 : NormalMatrix) 1 G H)

theorem scalarLift_one (N : ℕ) : scalarLift (1 : Matrix (Fin N) (Fin N) ℝ) = 1 :=
  Matrix.one_kronecker_one

theorem blockAt_scalarLift {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    blockAt (scalarLift G) i j = G i j • (1 : NormalMatrix) := by
  ext a b
  change (1 : NormalMatrix) a b * G i j = G i j * (1 : NormalMatrix) a b
  ring

theorem trace_eq_sum_block_traces {N : ℕ}
    (A : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) :
    A.trace = ∑ i, (blockAt A i i).trace := by
  simp only [Matrix.trace, Matrix.diag, blockAt, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- A scalar operation on the time nodes pairs only with the trace of each
normal curvature block. Cross-time commutation is not used. -/
theorem trace_scalarLift_mul_diagonal {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → NormalMatrix) :
    (scalarLift G * Matrix.blockDiagonal A).trace = ∑ i, G i i * (A i).trace := by
  rw [trace_eq_sum_block_traces]
  simp_rw [blockAt_mul_diagonal, blockAt_scalarLift, smul_mul_assoc,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

/-- The normalized perturbation has trace zero whenever every Weyl block
has trace zero, for any scalar time-node normalizer. -/
theorem trace_normalized_defect_zero {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0) :
    (scalarLift G * Matrix.blockDiagonal A * scalarLift G).trace = 0 := by
  rw [Matrix.trace_mul_cycle, ← scalarLift_mul, trace_scalarLift_mul_diagonal]
  simp only [hA, mul_zero, Finset.sum_const_zero]

/-- The trace of the normalized Jacobi matrix is precisely its dimension.
This is the trace bound used on the complementary block in compression. -/
theorem normalized_jacobi_trace {N : ℕ} (G L : Matrix (Fin N) (Fin N) ℝ)
    (A : Fin N → NormalMatrix) (a : ℝ)
    (hG : G * L * G = 1) (hA : ∀ i, (A i).trace = 0) :
    (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G).trace =
      3 * N := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, ← scalarLift_mul,
    ← scalarLift_mul, hG, scalarLift_one, Matrix.trace_one,
    mul_smul_comm, smul_mul_assoc, Matrix.trace_smul,
    trace_normalized_defect_zero G A hA]
  simp

end

end PositiveEinsteinFour.Jacobi

end OAI
