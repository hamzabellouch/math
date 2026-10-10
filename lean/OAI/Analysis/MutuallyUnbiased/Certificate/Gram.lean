import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Star.Real
import OAI.Analysis.MutuallyUnbiased.Certificate.Algebra

namespace OAI

/-!
# Exact rational Gram witnesses

A unit lower triangular matrix and a positive rational diagonal certify a real
matrix's positive definiteness. The large numerical checks can therefore be
split into separate rational identities for individual matrix entries.
-/
namespace MUB6.Certificate

open Matrix
open scoped BigOperators

/-- Complete a table of strict lower triangular entries with unit diagonal. -/
def lowerUnit {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if j < i then entries i j else if i = j then 1 else 0

/-- Interpret a rational matrix as a real matrix. -/
def realMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => A i j

@[simp] theorem lowerUnit_diag {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ)
    (i : Fin n) : lowerUnit entries i i = 1 := by simp [lowerUnit]

@[simp] theorem lowerUnit_above {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ)
    {i j : Fin n} (h : i < j) : lowerUnit entries i j = 0 := by
  simp [lowerUnit, not_lt_of_ge h.le, ne_of_lt h]

theorem real_lowerUnit_det {n : ℕ} (entries : Matrix (Fin n) (Fin n) ℚ) :
    (realMatrix (lowerUnit entries)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [realMatrix]
  · intro i j hij
    change i < j at hij
    change (lowerUnit entries i j : ℝ) = 0
    rw [lowerUnit_above entries hij]
    norm_num

/-- A collection of scalar rational checks certifies the full real Gram identity. -/
theorem real_gram_eq {n : ℕ} (Z U : Matrix (Fin n) (Fin n) ℚ) (D : Fin n → ℚ)
    (h : ∀ i j, Z i j = ∑ k, U k i * D k * U k j) :
    realMatrix Z = (realMatrix U)ᴴ * Matrix.diagonal (fun k => (D k : ℝ)) * realMatrix U := by
  ext i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have hij := congrArg (fun q : ℚ => (q : ℝ)) (h i j)
  simpa [realMatrix, Rat.cast_sum, Rat.cast_mul] using hij

/-- Soundness of a positive diagonal/unit-triangular Gram certificate. -/
theorem posDef_of_rational_gram {n : ℕ}
    (Z entries : Matrix (Fin n) (Fin n) ℚ) (D : Fin n → ℚ)
    (hD : ∀ i, 0 < D i)
    (hZ : ∀ i j, Z i j = ∑ k, lowerUnit entries k i * D k * lowerUnit entries k j) :
    (realMatrix Z).PosDef := by
  rw [real_gram_eq Z (lowerUnit entries) D hZ]
  apply Matrix.PosDef.conjTranspose_mul_mul_same
  · apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast hD i
  · apply Matrix.mulVec_injective_of_isUnit
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [real_lowerUnit_det]
    exact isUnit_one

end MUB6.Certificate

end OAI
