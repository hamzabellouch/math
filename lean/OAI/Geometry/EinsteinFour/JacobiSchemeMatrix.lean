import OAI.Geometry.EinsteinFour.JacobiScheme
import OAI.Geometry.EinsteinFour.JacobiPivots
import OAI.Geometry.EinsteinFour.ReferenceCompression

namespace OAI

/-! Identifying the concrete Jacobi recurrence with the finite curvature matrix. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem scalarLift_sub_diagonal {N : ℕ} (d a : ℝ) (A : Fin N → NormalMatrix) :
    scalarLift (scalarDirichlet N d) - a • Matrix.blockDiagonal A =
      dirichletMatrix (fun i => d • (1 : NormalMatrix) - a • A i) := by
  ext ⟨u, i⟩ ⟨v, j⟩
  by_cases hij : i = j
  · subst j
    simp [scalarLift, Matrix.kronecker, Matrix.kroneckerMap, scalarDirichlet,
      dirichletMatrix, Matrix.blockDiagonal, mul_comm]
  · by_cases hf : i.val + 1 = j.val
    · have hb : ¬j.val + 1 = i.val := by omega
      simp [scalarLift, Matrix.kronecker, Matrix.kroneckerMap, scalarDirichlet,
        dirichletMatrix, Matrix.blockDiagonal, hij, hf, hb]
    · by_cases hb : j.val + 1 = i.val <;>
        simp [scalarLift, Matrix.kronecker, Matrix.kroneckerMap, scalarDirichlet,
          dirichletMatrix, Matrix.blockDiagonal, hij, hf, hb]

theorem curvatureDirichlet_eq (t : ℝ) {N : ℕ} (A : Fin N → NormalMatrix) :
    curvatureDirichlet t A = dirichletMatrix (fun i =>
      (2 : ℝ) • (1 : NormalMatrix) - (t / (N + 1)) ^ 2 • (1 + A i)) := by
  rw [curvatureDirichlet, referenceMatrix, scalarLift_sub_diagonal]
  congr 1
  funext i
  module

/-- All diagonal blocks of the discrete Jacobi recurrence are the actual
curvature blocks. This identity includes the time-index shift. -/
theorem curvatureDirichlet_determinant {N : ℕ} {t : ℝ} (ht : t ≠ 0)
    (R : ℕ → NormalMatrix)
    (hsym : ∀ i, (R i).transpose = R i)
    (hunit : ∀ i, 1 ≤ i → i ≤ N + 1 →
      IsUnit (normalizedDiscrete R (t / (N + 1)) i).det) :
    (curvatureDirichlet t (fun i : Fin N => R (i.val + 1) - 1)).det =
      (normalizedDiscrete R (t / (N + 1)) (N + 1)).det := by
  have hh : t / (N + 1 : ℝ) ≠ 0 := div_ne_zero ht (by positivity)
  rw [curvatureDirichlet_eq]
  simp only [add_sub_cancel]
  apply dirichlet_determinant_eq_jacobi
    (fun i => (2 : ℝ) • (1 : NormalMatrix) - (t / (N + 1)) ^ 2 • R (i + 1))
    (normalizedDiscrete R (t / (N + 1))) N
  · intro i
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hsym]
  · exact normalizedDiscrete_zero _ _
  · exact normalizedDiscrete_one _ hh
  · exact normalizedDiscrete_recurrence R _
  · exact hunit

end

end PositiveEinsteinFour.Jacobi

end OAI
