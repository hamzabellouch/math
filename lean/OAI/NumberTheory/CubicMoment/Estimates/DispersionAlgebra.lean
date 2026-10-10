import OAI.NumberTheory.CubicMoment.Estimates.PublishedHecke

namespace OAI

/-!
# Exact corrected-dispersion identities

The polynomials below are those in `eq:dispersion-polynomials` of the
manuscript. The factorization is valid even with a common prime factor:
the already proved Gauss-sum multiplication law then makes the summand zero.
The norm estimates here do not assume the new dispersion bounds.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- The norm twist at real Mellin height `u`. -/
def normTwist (u : ℝ) (a : Eisenstein) : ℂ :=
  Complex.exp ((u * Real.log (norm a) : ℝ) * Complex.I)

@[simp] theorem norm_normTwist (u : ℝ) (a : Eisenstein) : ‖normTwist u a‖ = 1 := by
  simp [normTwist, Complex.norm_exp]

theorem normTwist_mul (u : ℝ) {a b : Eisenstein}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    normTwist u (a * b) = normTwist u a * normTwist u b := by
  have han : norm a ≠ 0 := (norm_eq_zero_iff.not.mpr ha)
  have hbn : norm b ≠ 0 := (norm_eq_zero_iff.not.mpr hb)
  have hn : norm (a * b) = norm a * norm b := Complex.normSq_mul _ _
  simp only [normTwist, hn, Real.log_mul han hbn, mul_add, Complex.ofReal_add,
    add_mul, Complex.exp_add]

/-- The polynomial `F_u(a)` in the corrected-dispersion argument. -/
def dispersionPolynomial (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (a : Eisenstein) : ℂ :=
  ∑ b ∈ B, β b * normTwist u b * gauss b * star (cubicSymbol b a)

/-- The model polynomial `S(u)`. -/
def dispersionModel (B : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ b ∈ B, β b * normTwist u b * ((norm b ^ (-1 / 6 : ℝ) : ℝ) : ℂ)

/-- The squarefree weight equals the squared absolute value of the normalized
Gauss sum, for primary elements. -/
theorem gauss_mul_star_squarefree {a : Eisenstein} (ha : primary a) :
    gauss a * star (gauss a) = if Squarefree a then (1 : ℂ) else 0 := by
  have hnorm := Complex.mul_conj' (gauss a)
  simp only [starRingEnd_apply] at hnorm
  rw [hnorm, norm_gauss ha]
  split_ifs <;> norm_num

theorem norm_gauss_le_one {a : Eisenstein} (ha : primary a) : ‖gauss a‖ ≤ 1 := by
  rw [norm_gauss ha]
  split_ifs <;> norm_num

/-- Exact factorization of the bilinear Gauss sum into the dispersion rows. -/
theorem bilinear_gauss_eq_rows (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b) :
    (∑ a ∈ A, ∑ b ∈ B, α a * β b * gauss (a * b) * normTwist u (a * b)) =
      ∑ a ∈ A, α a * normTwist u a * gauss a * dispersionPolynomial B β u a := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [dispersionPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [gauss_mul (hA a ha) (hB b hb),
    normTwist_mul u (primary_ne_zero (hA a ha)) (primary_ne_zero (hB b hb))]
  ring

/-- The corrected row polynomial. -/
def correctedDispersionPolynomial (B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (a : Eisenstein) : ℂ :=
  dispersionPolynomial B β u a -
    (cStar : ℂ) * star (gauss a) * ((norm a ^ (-1 / 6 : ℝ) : ℝ) : ℂ) *
      dispersionModel B β u

/-- The correction subtracts the factored model exactly, with the true
squarefree weight on the outer variable. Removing common prime factors
from the model is a separate arithmetic step. -/
theorem corrected_bilinear_identity (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ)
    (hA : ∀ a ∈ A, primary a) (hB : ∀ b ∈ B, primary b) :
    (∑ a ∈ A, ∑ b ∈ B, α a * β b * gauss (a * b) * normTwist u (a * b)) -
      (cStar : ℂ) * dispersionModel B β u *
        (∑ a ∈ A, α a * normTwist u a *
          (if Squarefree a then (1 : ℂ) else 0) * ((norm a ^ (-1 / 6 : ℝ) : ℝ) : ℂ)) =
      ∑ a ∈ A, α a * normTwist u a * gauss a *
        correctedDispersionPolynomial B β u a := by
  rw [bilinear_gauss_eq_rows A B α β u hA hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [correctedDispersionPolynomial]
  rw [← gauss_mul_star_squarefree (hA a ha)]
  simp only [starRingEnd_apply]
  ring

/-- Finite Cauchy--Schwarz for the actual complex row sum. -/
theorem complex_bilinear_rows_sq {ι : Type*} (A : Finset ι) (α F : ι → ℂ) :
    ‖∑ a ∈ A, α a * F a‖ ^ 2 ≤
      (∑ a ∈ A, ‖α a‖ ^ 2) * ∑ a ∈ A, ‖F a‖ ^ 2 := by
  calc
    _ ≤ (∑ a ∈ A, ‖α a * F a‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (norm_sum_le _ _) 2
    _ = (∑ a ∈ A, ‖α a‖ * ‖F a‖) ^ 2 := by simp_rw [norm_mul]
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq A _ _

/-- The outer Gauss sum and norm twist cost no more than the coefficient
energy. Thus the corrected variance gives the desired bilinear saving. -/
theorem corrected_bilinear_bound_sq (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) (hA : ∀ a ∈ A, primary a) :
    ‖∑ a ∈ A, α a * normTwist u a * gauss a *
        correctedDispersionPolynomial B β u a‖ ^ 2 ≤
      (∑ a ∈ A, ‖α a‖ ^ 2) *
        ∑ a ∈ A, ‖correctedDispersionPolynomial B β u a‖ ^ 2 := by
  apply (complex_bilinear_rows_sq A (fun a => α a * normTwist u a * gauss a)
    (correctedDispersionPolynomial B β u)).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Finset.sum_le_sum
  intro a ha
  simp only [norm_mul, norm_normTwist, mul_one]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_of_le_one_right (by positivity) (norm_gauss_le_one (hA a ha))) 2

end CubicFirstMoment

end

end OAI
