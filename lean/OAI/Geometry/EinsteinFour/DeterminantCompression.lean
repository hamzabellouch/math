import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

namespace OAI

/-! The determinant comparison used when the first sine mode is split off
from a discrete Jacobi matrix. The complementary block need not commute with
the first block or with the curvature matrices at other times. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- The trace form of the arithmetic-geometric mean estimate. -/
theorem det_le_exp_trace {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det ≤ Real.exp (A.trace - Fintype.card n) := by
  calc
    A.det = ∏ i, hA.isHermitian.eigenvalues i := by
      simpa using hA.isHermitian.det_eq_prod_eigenvalues
    _ ≤ ∏ i, Real.exp (hA.isHermitian.eigenvalues i - 1) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact hA.eigenvalues_nonneg i
      · intro i _
        have h := Real.add_one_le_exp (hA.isHermitian.eigenvalues i - 1)
        linarith
    _ = Real.exp (A.trace - Fintype.card n) := by
      rw [← Real.exp_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      congr 1
      simpa using hA.isHermitian.trace_eq_sum_eigenvalues.symm

theorem det_le_one_of_trace_le_card {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (htrace : A.trace ≤ Fintype.card n) :
    A.det ≤ 1 := by
  calc
    A.det ≤ Real.exp (A.trace - Fintype.card n) := det_le_exp_trace hA
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (sub_nonpos.mpr htrace)
    _ = 1 := Real.exp_zero

/-- Discarding the complementary modes costs no determinant when their
trace is at most their dimension. This is the finite-matrix step in the
upper radial comparison. -/
theorem det_fromBlocks_le_first {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Matrix m m ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    (hP : P.PosDef) (hA : (fromBlocks P C Cᴴ Q).PosSemidef)
    (htrace : Q.trace ≤ Fintype.card n) :
    (fromBlocks P C Cᴴ Q).det ≤ P.det := by
  let : Invertible P := hP.isUnit.invertible
  have hS : (Q - Cᴴ * P⁻¹ * C).PosSemidef :=
    (PosDef.fromBlocks₁₁ C Q hP).mp hA
  have hcost : 0 ≤ (Cᴴ * P⁻¹ * C).trace := by
    exact (hP.posSemidef.inv.conjTranspose_mul_mul_same C).trace_nonneg
  have hStrace : (Q - Cᴴ * P⁻¹ * C).trace ≤ Fintype.card n := by
    rw [trace_sub]
    linarith
  have hdet := det_le_one_of_trace_le_card hS hStrace
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  simpa using mul_le_mul_of_nonneg_left hdet hP.det_pos.le

/-- In a positive definite block matrix, the first compression is already
positive definite; no extra hypothesis on it is necessary. -/
theorem det_posDef_fromBlocks_le_first {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Matrix m m ℝ} {C : Matrix m n ℝ} {Q : Matrix n n ℝ}
    (hA : (fromBlocks P C Cᴴ Q).PosDef)
    (htrace : Q.trace ≤ Fintype.card n) :
    (fromBlocks P C Cᴴ Q).det ≤ P.det := by
  have hP : P.PosDef := by
    convert hA.submatrix Sum.inl_injective using 1
    ext i j
    rfl
  exact det_fromBlocks_le_first hP hA.posSemidef htrace

end

end PositiveEinsteinFour.Jacobi

end OAI
