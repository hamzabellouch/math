import OAI.Geometry.EinsteinFour.TensorPairing

namespace OAI

/-! The curvature commutator retained by the complete trace component. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

/-- The actual trace-free square of a diagonal Weyl block. -/
def diagonalSquareBlock (t : Fin 3 → ℝ) : Mat :=
  Matrix.diagonal (fun s => t s ^ 2 - (∑ r, t r ^ 2) / 3)

/-- The normalized weak Weyl equation in a diagonal frame. -/
def diagonalLaplacianBlock (t : Fin 3 → ℝ) : Mat :=
  Matrix.diagonal (fun s => 6 * (t s - (t s ^ 2 - (∑ r, t r ^ 2) / 3)))

/-- The scalar trace term disappears from the infinitesimal matrix action. -/
theorem matrixAction_diagonalSquare (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (s : Fin 3) :
    matrixAction s (diagonalSquareBlock t) =
      (-t s) • matrixAction s (Matrix.diagonal t) := by
  have ht2 : t 2 = -t 0 - t 1 := by
    have h := ht
    simp [Fin.sum_univ_succ] at h
    linarith
  ext a b
  change matrixAction s (diagonalSquareBlock t) a b =
    -t s * matrixAction s (Matrix.diagonal t) a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [diagonalSquareBlock, matrixAction, rotation, Matrix.diagonal,
      Fin.sum_univ_succ, ht2]
  all_goals ring

theorem matrixAction_diagonalLaplacian (t : Fin 3 → ℝ) (ht : ∑ s, t s = 0)
    (s : Fin 3) :
    matrixAction s (diagonalLaplacianBlock t) =
      (6 * (1 + t s)) • matrixAction s (Matrix.diagonal t) := by
  have ht2 : t 2 = -t 0 - t 1 := by
    have h := ht
    simp [Fin.sum_univ_succ] at h
    linarith
  ext a b
  change matrixAction s (diagonalLaplacianBlock t) a b =
    (6 * (1 + t s)) * matrixAction s (Matrix.diagonal t) a b
  fin_cases s <;> fin_cases a <;> fin_cases b <;>
    simp [diagonalLaplacianBlock, matrixAction, rotation, Matrix.diagonal,
      Fin.sum_univ_succ, ht2]
  all_goals ring

/-- The trace component retains its complete skew derivative part. -/
theorem traceComponent_skew (M : Mat) (i j : Fin 4) (a b : Fin 3) :
    traceComponent M i j a b - traceComponent M j i a b =
      (1 / 12) * ∑ s, quaternionMatrix s i j * matrixAction s M a b := by
  have hd : (if i = j then (3 / 5 : ℝ) * M a b else 0) =
      (if j = i then (3 / 5 : ℝ) * M a b else 0) := by simp [eq_comm]
  have hs (s : Fin 3) : quaternionMatrix s j i = -quaternionMatrix s i j :=
    quaternionMatrix_skew s j i
  change (5 / 12 : ℝ) * traceLift M i j a b -
      (5 / 12 : ℝ) * traceLift M j i a b = _
  unfold traceLift
  rw [← hd]
  simp_rw [hs, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- The trace component's skew part is exactly the Einstein curvature
commutator once the weak Weyl equation supplies its trace. -/
theorem traceComponent_diagonalLaplacian_skew (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) (i j : Fin 4) (a b : Fin 3) :
    traceComponent (diagonalLaplacianBlock t) i j a b -
      traceComponent (diagonalLaplacianBlock t) j i a b =
      (1 / 2) * ∑ s, (1 + t s) * quaternionMatrix s i j *
        matrixAction s (Matrix.diagonal t) a b := by
  rw [traceComponent_skew]
  have h (s : Fin 3) : matrixAction s (diagonalLaplacianBlock t) a b =
      (6 * (1 + t s)) * matrixAction s (Matrix.diagonal t) a b := by
    exact congrArg (fun M : Mat => M a b) (matrixAction_diagonalLaplacian t ht s)
  simp_rw [h]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Subtracting the prescribed trace component removes the actual curvature
commutator; derivative symmetry is a consequence, not an extra type premise. -/
theorem trace_subtracted_symmetric (X : Hessian) (t : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0)
    (hcomm : ∀ i j a b, X i j a b - X j i a b =
      (1 / 2) * ∑ s, (1 + t s) * quaternionMatrix s i j *
        matrixAction s (Matrix.diagonal t) a b) :
    ∀ i j, (X - traceComponent (diagonalLaplacianBlock t)) i j =
      (X - traceComponent (diagonalLaplacianBlock t)) j i := by
  intro i j
  ext a b
  change X i j a b - traceComponent (diagonalLaplacianBlock t) i j a b =
    X j i a b - traceComponent (diagonalLaplacianBlock t) j i a b
  have h := hcomm i j a b
  have hc := traceComponent_diagonalLaplacian_skew t ht i j a b
  linarith

end
end PositiveEinsteinFour.TraceHessian

end OAI
