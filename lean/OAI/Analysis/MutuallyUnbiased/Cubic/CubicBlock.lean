import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-! The three-by-three block obstruction in cubic classification, proved by
Newton's determinant identity instead of a dimension argument. -/

noncomputable section
open scoped BigOperators ComplexConjugate Matrix

namespace MUB6

theorem trace_newton_three (C : Matrix (Fin 3) (Fin 3) ℂ) :
    6 * C.det = C.trace ^ 3 - 3 * C.trace * (C * C).trace +
      2 * (C * C * C).trace := by
  simp [Matrix.det_fin_three, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

/-- A three-dimensional projection cannot have rank three halves.  This
formulation needs only polynomial identities over the complex numbers. -/
theorem no_three_by_three_scaled_projection (C : Matrix (Fin 3) (Fin 3) ℂ)
    (hC : C * C = (6 : ℂ) • C) (ht : C.trace = 9) : False := by
  have ht2 : (C * C).trace = 54 := by rw [hC, Matrix.trace_smul, ht]; norm_num
  have ht3 : (C * C * C).trace = 324 := by
    rw [hC, Matrix.smul_mul, hC, Matrix.trace_smul, Matrix.trace_smul, ht]
    norm_num
  have hn := trace_newton_three C
  rw [ht, ht2, ht3] at hn
  have hd : C.det = (-27 / 2 : ℂ) := by linear_combination hn / 6
  have hdm := congrArg Matrix.det hC
  rw [Matrix.det_mul, Matrix.det_smul, hd] at hdm
  norm_num at hdm

/-- The two classes of three restricted rows cannot be mutually orthogonal
when their combined columns are orthogonal and every entry has modulus one. -/
theorem no_cubic_three_by_three_block
    (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (hunit : ∀ i j, Complex.normSq (A i j) = 1)
    (hcross : A * B.conjTranspose = 0)
    (hcol : A.conjTranspose * A + B.conjTranspose * B = (6 : ℂ) • 1) : False := by
  let C := A.conjTranspose * A
  have hCD : C * (B.conjTranspose * B) = 0 := by
    dsimp [C]
    calc
      A.conjTranspose * A * (B.conjTranspose * B) =
          A.conjTranspose * (A * B.conjTranspose) * B := by
            simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hcross, Matrix.mul_zero, Matrix.zero_mul]
  have hC : C * C = (6 : ℂ) • C := by
    calc
      C * C = C * (C + B.conjTranspose * B) := by rw [Matrix.mul_add, hCD, add_zero]
      _ = C * ((6 : ℂ) • 1) := by rw [hcol]
      _ = (6 : ℂ) • C := by rw [Matrix.mul_smul, Matrix.mul_one]
  have ht : C.trace = 9 := by
    have hh (i j : Fin 3) : conj (A i j) * A i j = (1 : ℂ) := by
      rw [mul_comm, Complex.mul_conj, hunit]
      rfl
    change (∑ i, ∑ j, conj (A j i) * A j i) = 9
    norm_num [hh]
  exact no_three_by_three_scaled_projection C hC ht

end MUB6

end

end OAI
