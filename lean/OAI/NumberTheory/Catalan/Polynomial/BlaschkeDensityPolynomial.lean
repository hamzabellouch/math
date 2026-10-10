import Mathlib.Algebra.Polynomial.Eval.Defs
import OAI.NumberTheory.Catalan.Estimates.CauchyKernel

namespace OAI

noncomputable section
open Polynomial
open scoped BigOperators
namespace InternalCatalan

def blaschkeNodePolynomial {ι : Type*} (s : Finset ι) (x : ι → ℝ) : ℂ[X] :=
  ∏ i ∈ s, (X - C (x i : ℂ))

def blaschkeDensityNumerator {ι : Type*} (s : Finset ι) (x : ι → ℝ) (D : ℕ) : ℂ[X] :=
  X ^ D * ∏ i ∈ s, (1 - C (x i : ℂ) * X)

theorem blaschkeDensity_eq_product {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (z : ℂ) :
    blaschkeDensity s x D z = z ^ D * ∏ i ∈ s, (1 - (x i : ℂ) * z) / (z - (x i : ℂ)) := by
  unfold blaschkeDensity finiteBlaschke blaschkeFactor
  rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [inv_div]

theorem blaschkeDensity_eq_eval_div {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (D : ℕ) (z : ℂ) :
    blaschkeDensity s x D z =
      (blaschkeDensityNumerator s x D).eval z / (blaschkeNodePolynomial s x).eval z := by
  simp only [blaschkeDensityNumerator, blaschkeNodePolynomial, eval_mul, eval_pow,
    eval_X, eval_prod, eval_sub, eval_one, eval_C]
  rw [blaschkeDensity_eq_product, Finset.prod_div_distrib]
  ring

theorem blaschkeNodePolynomial_eval_ne_zero_iff {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (z : ℂ) :
    (blaschkeNodePolynomial s x).eval z ≠ 0 ↔ ∀ i ∈ s, z ≠ (x i : ℂ) := by
  simp only [blaschkeNodePolynomial, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_ne_zero_iff, sub_ne_zero]

theorem blaschkeNodePolynomial_eval_imaginary_ne_zero {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ s, x i ≠ 0) (u : ℝ) :
    (blaschkeNodePolynomial s x).eval (Complex.I * (u : ℂ)) ≠ 0 := by
  apply (blaschkeNodePolynomial_eval_ne_zero_iff s x _).mpr
  intro i hi h
  have hre : (0 : ℝ) = x i := by
    simpa [Complex.mul_re, Complex.mul_im] using congrArg Complex.re h
  exact hx i hi hre.symm

end InternalCatalan

end

end OAI
