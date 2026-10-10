import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixExponential
import Mathlib.Analysis.Complex.Exponential

namespace OAI

/-! # Complex upper triangular matrix exponentials -/

noncomputable section
namespace PolycyclicRecognition
open scoped Matrix.Norms.Operator
variable {n : ℕ}

theorem complex_triangular_mul_diag (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

private theorem entry_hasSum (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (A ^ k) i j) (NormedSpace.exp A i j) := by
  let ev : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).map
    ev.toContinuousLinearMap ev.toContinuousLinearMap.continuous

theorem complex_matrix_exp_upperTriangular (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) : (NormedSpace.exp A).IsUpperTriangular := by
  intro i j hji
  have hs := entry_hasSum A i j
  have hz : (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (A ^ k) i j) = fun _ => 0 := by
    funext k
    rw [(hA.pow k) hji, mul_zero]
  rw [hz] at hs
  exact hs.unique hasSum_zero

theorem complex_matrix_exp_diagonal (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (i : Fin n) :
    NormedSpace.exp A i i = Complex.exp (A i i) := by
  have hp (k : ℕ) : (A ^ k) i i = (A i i) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, complex_triangular_mul_diag _ _ (hA.pow k) hA, ih, pow_succ]
  have hs := entry_hasSum A i i
  simp only [hp] at hs
  have ht : HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * (A i i) ^ k)
      (Complex.exp (A i i)) := by
    simpa only [smul_eq_mul, ← Complex.exp_eq_exp_ℂ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (A i i)
  exact hs.unique ht

end PolycyclicRecognition

end

end OAI
