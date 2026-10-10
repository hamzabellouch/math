import OAI.LinearAlgebra.CirculantHadamard.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

namespace OAI

namespace CirculantHadamard

def firstRow_one : Fin 1 → ℝ := ![1]

def firstRow_four : Fin 4 → ℝ := ![1, 1, 1, -1]

def witness_one : Matrix (Fin 1) (Fin 1) ℝ := !![1]

def witness_four : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, -1;
    -1, 1, 1, 1;
     1, -1, 1, 1;
     1, 1, -1, 1]

@[simp] theorem witness_one_first_row : witness_one 0 = firstRow_one := rfl

@[simp] theorem witness_four_first_row : witness_four 0 = firstRow_four := rfl

theorem witness_one_eq_rowCirculant : witness_one = rowCirculant firstRow_one := by
  ext i j
  fin_cases i; fin_cases j; rfl

theorem witness_four_eq_rowCirculant : witness_four = rowCirculant firstRow_four := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem witness_one_signs (i j : Fin 1) : IsSign (witness_one i j) := by
  fin_cases i; fin_cases j; norm_num [IsSign, witness_one]

theorem witness_four_signs (i j : Fin 4) : IsSign (witness_four i j) := by
  fin_cases i <;> fin_cases j <;> norm_num [IsSign, witness_four]

theorem witness_one_gram :
    witness_one * witness_one.transpose = (1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul_apply, Fin.sum_univ_one, witness_one,
    Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply]

theorem witness_four_gram :
    witness_four * witness_four.transpose = (4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four, witness_four,
      Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem witness_one_isCirculant : IsCirculant witness_one := by
  rw [witness_one_eq_rowCirculant]
  exact rowCirculant_isCirculant firstRow_one

theorem witness_four_isCirculant : IsCirculant witness_four := by
  rw [witness_four_eq_rowCirculant]
  exact rowCirculant_isCirculant firstRow_four

theorem witness_one_isSignHadamard : IsSignHadamard witness_one := by
  exact ⟨witness_one_signs, by simpa using witness_one_gram⟩

theorem witness_four_isSignHadamard : IsSignHadamard witness_four := by
  exact ⟨witness_four_signs, by simpa using witness_four_gram⟩

theorem exists_one : ExistsRealCirculantHadamard 1 :=
  ⟨witness_one, witness_one_isCirculant, witness_one_isSignHadamard⟩

theorem exists_four : ExistsRealCirculantHadamard 4 :=
  ⟨witness_four, witness_four_isCirculant, witness_four_isSignHadamard⟩

/-- The explicit matrices of orders one and four establish existence. -/
theorem exists_of_order_one_or_four {n : ℕ} (hn : n = 1 ∨ n = 4) :
    ExistsRealCirculantHadamard n := by
  rcases hn with rfl | rfl
  · exact exists_one
  · exact exists_four

end CirculantHadamard

end OAI
