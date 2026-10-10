import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryHornerEvaluation
import Mathlib.Algebra.Polynomial.Expand

namespace OAI

/-! # Recovering the raw determinant from its sixteen even coefficients -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate

attribute [local irreducible] rawDeterminant determinant state polynomialState

theorem coefficientPolynomial_coeff (as : List ℂ) (n : ℕ) :
    (coefficientPolynomial as).coeff n = as[n]?.getD 0 := by
  induction as generalizing n with
  | nil => simp [coefficientPolynomial]
  | cons a as ih =>
    cases n with
    | zero => simp [coefficientPolynomial]
    | succ n => simp [coefficientPolynomial, coeff_X_mul, ih]

theorem coefficientPolynomial_evenValues (ell : ℕ) (b Z : ℝ) (n : ℕ) :
    (coefficientPolynomial (evenValues ell b Z)).coeff n =
      (rawDeterminant ell b Z).coeff (2 * n) := by
  rw [coefficientPolynomial_coeff]
  by_cases hn : n < 16
  · simp only [evenValues, List.getElem?_map, List.getElem?_range hn, Option.map_some,
      Option.getD_some]
  · have hn' : (List.range 16)[n]? = none := List.getElem?_eq_none (by simp; omega)
    simp only [evenValues, List.getElem?_map, hn', Option.map_none, Option.getD_none]
    exact (coeff_eq_zero_of_natDegree_lt ((rawDeterminant_degree ell b Z).trans_lt (by omega))).symm

theorem rawDeterminant_eq_expand_even (ell : ℕ) (b Z : ℝ) :
    expand ℂ 2 (coefficientPolynomial (evenValues ell b Z)) = rawDeterminant ell b Z := by
  ext n
  rw [coeff_expand (by decide : 0 < 2)]
  split_ifs with hd
  · rw [coefficientPolynomial_evenValues]
    congr 1
    omega
  · rcases Nat.even_or_odd n with he | ho
    · exact (hd he.two_dvd).elim
    · exact (rawDeterminant_coeff_odd ell b Z n ho).symm

theorem rawDeterminant_eval_square (ell : ℕ) (b Z v : ℝ) :
    (rawDeterminant ell b Z).eval (v : ℂ) =
      (coefficientPolynomial (evenValues ell b Z)).eval ((v ^ 2 : ℝ) : ℂ) := by
  rw [← rawDeterminant_eq_expand_even, expand_eval]
  norm_cast

end DefocusingNLS.BoundaryCertificate

end OAI
