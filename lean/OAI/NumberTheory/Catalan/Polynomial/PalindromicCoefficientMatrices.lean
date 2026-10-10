import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.NormNum

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def palindromicU (p l : ℕ) : (ZMod p)[X] :=
  (2 * X) ^ l * (1 + X ^ 2) ^ (p - 1 - l)

def palindromicQ (p i : ℕ) : (ZMod p)[X] :=
  X ^ i * ∑ j ∈ Finset.range (p - i), X ^ (2 * j)

theorem palindromicU_factor (p l : ℕ) :
    palindromicU p l =
      C ((2 : ZMod p) ^ l) * (X ^ l * (1 + X ^ 2) ^ (p - 1 - l)) := by
  simp [palindromicU, mul_pow, mul_assoc, Polynomial.C_ofNat]

theorem palindromicU_coeff_below (p l : ℕ) {k : ℕ} (hk : k < l) :
    (palindromicU p l).coeff k = 0 := by
  rw [palindromicU_factor, coeff_C_mul, coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]

theorem palindromicU_coeff_self (p l : ℕ) :
    (palindromicU p l).coeff l = (2 : ZMod p) ^ l := by
  rw [palindromicU_factor, coeff_C_mul, coeff_X_pow_mul',
    ite_eq_left le_rfl, Nat.sub_self]
  change (2 : ZMod p) ^ l * constantCoeff ((1 + X ^ 2) ^ (p - 1 - l)) = _
  have hx : constantCoeff (X : (ZMod p)[X]) = 0 := by
    change (X : (ZMod p)[X]).coeff 0 = 0
    simp
  rw [map_pow, map_add, map_one, map_pow, hx]
  simp

theorem palindromicQ_coeff_below (p i : ℕ) {k : ℕ} (hk : k < i) :
    (palindromicQ p i).coeff k = 0 := by
  rw [palindromicQ, coeff_X_pow_mul', ite_eq_right (by omega)]

theorem palindromicQ_coeff_self {p i : ℕ} (hi : i < p) :
    (palindromicQ p i).coeff i = 1 := by
  classical
  rw [palindromicQ, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
    finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hne
    simp [coeff_X_pow, hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

end InternalCatalan

end



noncomputable section

namespace InternalCatalan

open scoped BigOperators

def palindromicUCoeffMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun k l => (palindromicU p l.val).coeff k.val

def palindromicQCoeffMatrix (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun k i => (palindromicQ p i.val).coeff k.val

theorem palindromicUCoeffMatrix_lower (p : ℕ) :
    (palindromicUCoeffMatrix p).IsLowerTriangular := by
  intro k l hkl
  exact palindromicU_coeff_below p l.val hkl

theorem palindromicQCoeffMatrix_lower (p : ℕ) :
    (palindromicQCoeffMatrix p).IsLowerTriangular := by
  intro k i hki
  exact palindromicQ_coeff_below p i.val hki

theorem det_palindromicUCoeffMatrix (p : ℕ) :
    (palindromicUCoeffMatrix p).det = ∏ l : Fin p, (2 : ZMod p) ^ l.val := by
  rw [Matrix.det_of_isLowerTriangular _ (palindromicUCoeffMatrix_lower p)]
  simp only [palindromicUCoeffMatrix, palindromicU_coeff_self]

theorem det_palindromicQCoeffMatrix (p : ℕ) :
    (palindromicQCoeffMatrix p).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (palindromicQCoeffMatrix_lower p)]
  have hdiag : ∀ i : Fin p, palindromicQCoeffMatrix p i i = 1 := by
    intro i
    exact palindromicQ_coeff_self i.isLt
  simp only [hdiag, Finset.prod_const_one]

theorem palindromic_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have hd : p ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

theorem det_palindromicUCoeffMatrix_ne_zero {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : (palindromicUCoeffMatrix p).det ≠ 0 := by
  rw [det_palindromicUCoeffMatrix]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  exact pow_ne_zero _ (palindromic_two_ne_zero hp2)

theorem det_palindromicQCoeffMatrix_ne_zero {p : ℕ} [Fact p.Prime] :
    (palindromicQCoeffMatrix p).det ≠ 0 := by
  rw [det_palindromicQCoeffMatrix]
  exact one_ne_zero

end InternalCatalan

end

end OAI
