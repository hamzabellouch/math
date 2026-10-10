import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixHeight
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace OAI

/-! # Diagonal entries of an upper triangular matrix exponential -/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem matrix_exp_entry_hasSum (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A ^ k) i j) (NormedSpace.exp A i j) := by
  let ev : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun B => B i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let f := ev.toContinuousLinearMap
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map f f.continuous
  change HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A ^ k) i j)
    (NormedSpace.exp A i j) at hs
  exact hs

theorem matrix_exp_upperTriangular (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) : (NormedSpace.exp A).IsUpperTriangular := by
  intro i j hji
  have hs := matrix_exp_entry_hasSum A i j
  have hz : (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A ^ k) i j) = fun _ => 0 := by
    funext k
    rw [(hA.pow k) hji, mul_zero]
  rw [hz] at hs
  exact hs.unique hasSum_zero

theorem matrix_exp_diagonal (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (i : Fin n) :
    NormedSpace.exp A i i = Real.exp (A i i) := by
  have hp (k : ℕ) : (A ^ k) i i = (A i i) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, triangular_mul_diag _ _ (hA.pow k) hA, ih, pow_succ]
  have hs := matrix_exp_entry_hasSum A i i
  simp only [hp] at hs
  have ht : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * (A i i) ^ k)
      (Real.exp (A i i)) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (A i i)
  exact hs.unique ht

end PolycyclicRecognition

end

end OAI
