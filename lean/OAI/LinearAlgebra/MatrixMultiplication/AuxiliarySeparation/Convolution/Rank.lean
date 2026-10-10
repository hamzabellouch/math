import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
import Mathlib.LinearAlgebra.Lagrange

namespace OAI

/-!
# Polynomial convolution by evaluation and interpolation

Evaluating the two input polynomials at `a + b - 1` distinct complex points,
then interpolating their product, expresses the convolution tensor as a sum
of `a + b - 1` rank-one tensors. This is the polynomial multiplication rank
upper bound used in Section 5.
-/

open scoped BigOperators
open Polynomial

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- Recover each monomial coefficient from evaluations at distinct nodes. -/
lemma monomial_coeff_eq_sum_interpolation {n m : ℕ} (hm : m < n)
    (v : Fin n → ℂ) (hv : Function.Injective v) (k : ℕ) :
    (if m = k then (1 : ℂ) else 0) =
      ∑ r : Fin n, v r ^ m * (Lagrange.basis Finset.univ v r).coeff k := by
  have hdeg : (X ^ m : ℂ[X]).degree < (Finset.univ : Finset (Fin n)).card := by
    simpa using hm
  have hpoly := Lagrange.eq_interpolate (f := (X ^ m : ℂ[X])) hv.injOn hdeg
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff k) hpoly
  simpa only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow, eq_comm] using hcoeff

/-- Evaluation at distinct nodes and Lagrange interpolation give an explicit
rank-one decomposition of polynomial convolution. -/
theorem convolution_eq_sum_rankOne {a b : ℕ}
    (v : Fin (a + b - 1) → ℂ) (hv : Function.Injective v) :
    convolution a b = fun i j k => ∑ r : Fin (a + b - 1),
      Tensor.rankOne (fun i : Fin a => v r ^ i.val)
        (fun j : Fin b => v r ^ j.val)
        (fun k : Fin (a + b - 1) => (Lagrange.basis Finset.univ v r).coeff k.val)
        i j k := by
  funext i j k
  have hij : i.val + j.val < a + b - 1 := (convolutionOutput i j).isLt
  simpa only [convolution_apply, Tensor.rankOne, pow_add] using
    monomial_coeff_eq_sum_interpolation hij v hv k.val

/-- The convolution tensor `C(a,b)` has rank at most `a + b - 1` over `ℂ`. -/
theorem convolution_rankAtMost (a b : ℕ) :
    Tensor.RankAtMost (convolution a b) (a + b - 1) := by
  let v : Fin (a + b - 1) → ℂ := fun r => r.val
  have hv : Function.Injective v := by
    intro i j h
    apply Fin.ext
    change (i.val : ℂ) = j.val at h
    exact_mod_cast h
  rw [convolution_eq_sum_rankOne v hv]
  simpa using Tensor.rankAtMost_sum_rankOne
    (fun r (i : Fin a) => v r ^ i.val)
    (fun r (j : Fin b) => v r ^ j.val)
    (fun r (k : Fin (a + b - 1)) => (Lagrange.basis Finset.univ v r).coeff k.val)

/-- The interpolation algorithm also bounds border rank. -/
theorem convolution_borderRankAtMost (a b : ℕ) :
    Tensor.BorderRankAtMost (convolution a b) (a + b - 1) :=
  (convolution_rankAtMost a b).borderRankAtMost

end MatrixMultiplication.AuxiliarySeparation

end OAI
