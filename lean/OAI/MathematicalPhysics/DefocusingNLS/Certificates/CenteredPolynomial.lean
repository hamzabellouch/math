import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RootDiskArithmetic
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingPolynomialDegree
import Mathlib.Algebra.Polynomial.Taylor

namespace OAI

/-! # Denominator-cleared Taylor coefficients for the disk certificates -/

open Polynomial

namespace DefocusingNLS.SeparatorArithmetic

noncomputable section

/-- The full unscaled winding polynomial, with integer coefficients. -/
def windingPolynomial (ℓ : ℕ) : Polynomial ℤ :=
  ∑ n ∈ Finset.range 16, monomial n (windingCoefficient ℓ n)

theorem coeff_windingPolynomial (ℓ j : ℕ) :
    (windingPolynomial ℓ).coeff j = windingCoefficient ℓ j := by
  classical
  by_cases hj : j < 16
  · simp [windingPolynomial, coeff_monomial, hj]
  · rw [windingCoefficient_eq_zero ℓ j (by omega)]
    simp [windingPolynomial, coeff_monomial, hj]

/-- The coefficient description holds at every order, including the vanishing
tail, so this polynomial is exactly the coefficientwise imaginary product. -/
theorem windingPolynomial_matches_product (ℓ j : ℕ) :
    (windingPolynomial ℓ).coeff j =
      ((toPolynomial (backwardCoefficients ℓ).1 *
        (toPolynomial (backwardCoefficients ℓ).2).map
          (starRingEnd GaussianInt)).coeff j).im := by
  rw [coeff_windingPolynomial, windingCoefficient_eq]

theorem coeff_taylor_finite (A : ℕ → GaussianInt) (c : GaussianInt)
    (i : ℕ) (hi : i ≤ 16) :
    (taylor c (∑ n ∈ Finset.range 16, monomial n (A n))).coeff i =
      ∑ j ∈ Finset.range (16 - i),
        A (j + i) * (Nat.choose (j + i) i : GaussianInt) * c ^ j := by
  rw [taylor_coeff, map_sum]
  simp only [hasseDeriv_monomial, eval_finsetSum, eval_monomial]
  conv_lhs => rw [← Nat.add_sub_of_le hi, Finset.sum_range_add]
  have hzero : ∑ n ∈ Finset.range i,
      (Nat.choose n i : GaussianInt) * A n * c ^ (n - i) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn), Nat.cast_zero,
      zero_mul]
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.add_sub_cancel_left]
  simp only [Nat.add_comm i j]
  ring

/-- Polynomial before translation, with the scaling denominator cleared. -/
def scaledSeparatorPolynomial (ℓ : ℕ) : Polynomial GaussianInt :=
  ∑ n ∈ Finset.range 16,
    monomial n ((windingCoefficient ℓ n * diskScale ^ (15 - n) : ℤ) : GaussianInt)

theorem centeredCoefficient_eq (ℓ : ℕ) (c : GaussianInt) (i : ℕ) (hi : i ≤ 16) :
    centeredCoefficient ℓ c i = (taylor c (scaledSeparatorPolynomial ℓ)).coeff i := by
  rw [scaledSeparatorPolynomial, coeff_taylor_finite _ _ _ hi]
  unfold centeredCoefficient
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

end
end DefocusingNLS.SeparatorArithmetic

end OAI
