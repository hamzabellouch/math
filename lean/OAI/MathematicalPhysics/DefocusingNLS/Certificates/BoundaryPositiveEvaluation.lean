import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryCertificatePositivity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryCertificateSemantics

namespace OAI

/-! # Positive evaluation from the exact coefficient checks -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate
open GaussianEnclosure

theorem positiveFirst16_spec (as : EnclosurePolynomial) (h : positiveFirst16 as = true)
    (n : ℕ) (hn : n < 16) :
    (as[n]?.getD zero).error < (as[n]?.getD zero).center.re := by
  have hh : ∀ j, j < 16 → (as[j]?.getD zero).error < (as[j]?.getD zero).center.re := by
    simpa [positiveFirst16, coefficientPositive, List.all_eq_true] using h
  exact hh n hn

theorem positiveFirst16_coefficients (as : EnclosurePolynomial) (p : Polynomial ℂ)
    (h : positiveFirst16 as = true) (hp : EnclosesPolynomial as p)
    (n : ℕ) (hn : n < 16) : 0 < (p.coeff n).re :=
  realPart_pos (coefficient_sound hp n) (positiveFirst16_spec as h n hn)

theorem eval_re_eq_sum16 (p : Polynomial ℂ) (hp : p.natDegree ≤ 15) (w : ℝ) :
    (p.eval (w : ℂ)).re = ∑ n ∈ Finset.range 16, (p.coeff n).re * w ^ n := by
  conv_lhs => rw [p.as_sum_range' 16 (by omega)]
  simp only [eval_finsetSum, eval_monomial, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hr : ((w : ℂ) ^ n).re = w ^ n := by
    rw [← Complex.ofReal_pow]
    rfl
  have hi : ((w : ℂ) ^ n).im = 0 := by
    rw [← Complex.ofReal_pow]
    rfl
  rw [Complex.mul_re, hr, hi]
  ring

/-- Every nonnegative evaluation is positive, including the constant endpoint. -/
theorem positive_eval_of_positiveFirst16 (as : EnclosurePolynomial) (p : Polynomial ℂ)
    (h : positiveFirst16 as = true) (hp : EnclosesPolynomial as p)
    (hdeg : p.natDegree ≤ 15) (w : ℝ) (hw : 0 ≤ w) : 0 < (p.eval (w : ℂ)).re := by
  rw [eval_re_eq_sum16 p hdeg w]
  apply Finset.sum_pos'
  · intro n hn
    exact mul_nonneg (positiveFirst16_coefficients as p h hp n (Finset.mem_range.mp hn)).le
      (pow_nonneg hw n)
  · refine ⟨0, by simp, ?_⟩
    simpa using positiveFirst16_coefficients as p h hp 0 (by decide)

end DefocusingNLS.BoundaryCertificate

end OAI
