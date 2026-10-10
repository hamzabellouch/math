import OAI.MathematicalPhysics.DefocusingNLS.Certificates.SeparatorArithmetic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

namespace OAI

/-!
# Polynomial meaning of the integer separator calculation

Interpreting the coefficient lists as polynomials identifies their recurrence
with the backward matrix product and its coefficientwise imaginary part.
-/

open Polynomial

namespace DefocusingNLS.SeparatorArithmetic

/-- Ascending coefficient lists interpreted as polynomials. -/
noncomputable def toPolynomial : List GaussianInt → Polynomial GaussianInt
  | [] => 0
  | a :: as => C a + X * toPolynomial as

theorem toPolynomial_add (xs ys : List GaussianInt) :
    toPolynomial (addCoefficients xs ys) = toPolynomial xs + toPolynomial ys := by
  induction xs generalizing ys with
  | nil => simp [addCoefficients, toPolynomial]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addCoefficients, toPolynomial]
    | cons y ys =>
      simp only [addCoefficients, toPolynomial, ih, map_add]
      ring

theorem toPolynomial_scale (a : GaussianInt) (xs : List GaussianInt) :
    toPolynomial (scaleCoefficients a xs) = C a * toPolynomial xs := by
  induction xs with
  | nil => simp [scaleCoefficients, toPolynomial]
  | cons x xs ih =>
    simp only [scaleCoefficients, List.map_cons, toPolynomial] at *
    rw [ih, map_mul]
    ring

theorem toPolynomial_mulLinear (a : GaussianInt) (xs : List GaussianInt) :
    toPolynomial (mulLinear a xs) =
      (C a + C (scale : GaussianInt) * X) * toPolynomial xs := by
  rw [mulLinear, toPolynomial_add, toPolynomial]
  simp only [map_zero, zero_add, toPolynomial_scale]
  ring

theorem coeff_toPolynomial (xs : List GaussianInt) (j : ℕ) :
    (toPolynomial xs).coeff j = xs[j]?.getD 0 := by
  induction xs generalizing j with
  | nil => simp [toPolynomial]
  | cons x xs ih =>
    cases j with
    | zero => simp [toPolynomial]
    | succ j => simp [toPolynomial, ih, coeff_X_mul]

/-- The list update for the first matching coordinate is the polynomial
matrix update specified in the appendix. -/
theorem toPolynomial_backwardStep_fst (ℓ n : ℕ)
    (xy : List GaussianInt × List GaussianInt) :
    toPolynomial (backwardStep ℓ n xy).1 =
      (C (⟨scale * n + 50000000 * ℓ - 3125000, -centerB⟩ : GaussianInt) +
        C (scale : GaussianInt) * X - C (⟨scale * (ℓ + 5), centerZ⟩ : GaussianInt)) *
        toPolynomial xy.1 - C (⟨0, centerZ⟩ : GaussianInt) * toPolynomial xy.2 := by
  simp only [backwardStep, toPolynomial_add, toPolynomial_mulLinear,
    toPolynomial_scale, map_sub]
  have h : (⟨0, -centerZ⟩ : GaussianInt) = -⟨0, centerZ⟩ := by ext <;> simp
  rw [h, map_neg]
  ring

theorem toPolynomial_backwardStep_snd (ℓ n : ℕ)
    (xy : List GaussianInt × List GaussianInt) :
    toPolynomial (backwardStep ℓ n xy).2 =
      (C (⟨scale * n + 50000000 * ℓ - 3125000, -centerB⟩ : GaussianInt) +
        C (scale : GaussianInt) * X) * (toPolynomial xy.1 + toPolynomial xy.2) := by
  simp only [backwardStep, toPolynomial_mulLinear, toPolynomial_add]

/-- Imaginary part as an additive homomorphism, for coefficient sums. -/
def imaginaryPart : GaussianInt →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' _ _ := rfl

theorem imaginaryPart_apply (z : GaussianInt) : imaginaryPart z = z.im := rfl

theorem coefficients_product_im (xs ys : List GaussianInt) (j : ℕ) :
    ((List.range (j + 1)).map fun k =>
      (xs[k]?.getD 0 * star (ys[j - k]?.getD 0)).im).sum =
      ((toPolynomial xs * (toPolynomial ys).map (starRingEnd GaussianInt)).coeff j).im := by
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_toPolynomial, coeff_map, starRingEnd_apply]
  simpa only [Nat.succ_eq_add_one, imaginaryPart_apply] using
    (map_sum imaginaryPart (fun k => xs[k]?.getD 0 * star (ys[j - k]?.getD 0))
      (Finset.range (j + 1))).symm

/-- The exact integer `pⱼ` is the imaginary part of the product coefficient
`[X^j] x(X) conj(y)(X)`; no numeric translation is assumed. -/
theorem windingCoefficient_eq (ℓ j : ℕ) :
    windingCoefficient ℓ j =
      ((toPolynomial (backwardCoefficients ℓ).1 *
        (toPolynomial (backwardCoefficients ℓ).2).map (starRingEnd GaussianInt)).coeff j).im := by
  exact coefficients_product_im _ _ _

end DefocusingNLS.SeparatorArithmetic

end OAI
