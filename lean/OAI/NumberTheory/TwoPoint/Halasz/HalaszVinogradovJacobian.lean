import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace OAI

/-! The Vandermonde Jacobian used in the nonsingular congruence step of
the complete-system mean-value argument. The polynomial form also covers
the lower-degree terms introduced by translation and differencing. -/
namespace TwoPointCorrelations

open Finset Polynomial Matrix

theorem halasz_vinogradov_polynomial_jacobian {R : Type*} [CommRing R] {k : ℕ}
    (P : Fin k → R[X]) (x : Fin k → R)
    (hdeg : ∀ j, (P j).natDegree ≤ j.val+1) :
    (Matrix.of (fun i j => (P j).derivative.eval (x i))).det =
      (∏ j, (P j).coeff (j.val+1)*(j.val+1:R)) * (Matrix.vandermonde x).det := by
  classical
  have hd (j : Fin k) : (P j).derivative.natDegree ≤ j.val := by
    have hh := (Polynomial.natDegree_derivative_le (P j)).trans
      (Nat.sub_le_sub_right (hdeg j) 1)
    simpa using hh
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials x
      (fun j => (P j).derivative) hd,Matrix.det_mul,
    Matrix.det_of_isUpperTriangular
      (Matrix.matrixOfPolynomials_isUpperTriangular (fun j => (P j).derivative) hd)]
  simp only [Matrix.of_apply,Polynomial.coeff_derivative]
  exact mul_comm _ _

theorem halasz_vinogradov_power_jacobian {R : Type*} [CommRing R] {k : ℕ}
    (x : Fin k → R) :
    (Matrix.of (fun i j => (j.val+1:R)*x i^j.val)).det =
      (k.factorial:R)*(Matrix.vandermonde x).det := by
  classical
  have hprod : (∏ j : Fin k, (j.val+1:R)) = (k.factorial:R) := by
    rw [Nat.factorial_eq_prod_range_add_one,Nat.cast_prod,← Fin.prod_univ_eq_prod_range]
    simp only [Nat.cast_add,Nat.cast_one]
  have h := Matrix.det_mul_row (fun j : Fin k => (j.val+1:R)) (Matrix.vandermonde x)
  simpa only [Matrix.vandermonde,Matrix.of_apply,hprod] using h

theorem halasz_vinogradov_jacobian_nonsingular {p k : ℕ} [Fact p.Prime]
    (hkp : k<p) (P : Fin k → (ZMod p)[X]) (x : Fin k → ZMod p)
    (hdeg : ∀ j, (P j).natDegree ≤ j.val+1)
    (hcoeff : ∀ j, (P j).coeff (j.val+1)≠0) (hx : Function.Injective x) :
    (Matrix.of (fun i j => (P j).derivative.eval (x i))).det ≠ 0 := by
  rw [halasz_vinogradov_polynomial_jacobian P x hdeg]
  apply mul_ne_zero
  · apply prod_ne_zero_iff.mpr
    intro j _
    apply mul_ne_zero (hcoeff j)
    have hj : j.val+1<p := by omega
    have hn : ((j.val+1:ℕ):ZMod p)≠0 :=
      (ZMod.natCast_eq_zero_iff _ _).not.mpr
        (Nat.not_dvd_of_pos_of_lt (by omega : 0<j.val+1) hj)
    simpa only [Nat.cast_add,Nat.cast_one] using hn
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hx

end TwoPointCorrelations

end OAI
