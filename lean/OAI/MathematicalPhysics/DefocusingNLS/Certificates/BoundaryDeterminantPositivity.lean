import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryChartCover

namespace OAI

/-! # Positivity of the coherent raw boundary determinant -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate

attribute [local irreducible] GaussianEnclosure.EnclosesPolynomial
  rawDeterminant evenValues homogeneousHorner transformed

theorem certificate_first (ell : Fin 4) : positiveFirst16 (transformed ell 0 1 1) = true := by
  fin_cases ell
  · exact row_zero_first_positive
  · exact row_one_first_positive
  · exact row_two_first_positive
  · exact row_three_first_positive

theorem certificate_second (ell : Fin 4) : positiveFirst16 (transformed ell 1 10 1) = true := by
  fin_cases ell
  · exact row_zero_second_positive
  · exact row_one_second_positive
  · exact row_two_second_positive
  · exact row_three_second_positive

theorem certificate_third (ell : Fin 4) : positiveFirst16 (transformed ell 10 1 0) = true := by
  fin_cases ell
  · exact row_zero_third_positive
  · exact row_one_third_positive
  · exact row_two_third_positive
  · exact row_three_third_positive

theorem chart_value_positive (ell : Fin 4) (b Z t : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (ht : 0 ≤ t) (U V J : ℤ) (hd : 0 < 1 + (J : ℝ) * t)
    (hcert : positiveFirst16 (transformed ell U V J) = true) :
    0 < ((coefficientPolynomial (evenValues ell b Z)).eval
      ((((U : ℝ) + (V : ℝ) * t) / (1 + (J : ℝ) * t) : ℝ) : ℂ)).re := by
  have hn : (chartNumerator U V).eval (t : ℂ) = ((((U : ℝ) + (V : ℝ) * t) : ℝ) : ℂ) := by
    simp [chartNumerator]
    ring
  have hden : (chartDenominator J).eval (t : ℂ) = (((1 + (J : ℝ) * t) : ℝ) : ℂ) := by
    simp [chartDenominator]
    ring
  have hden0 : (chartDenominator J).eval (t : ℂ) ≠ 0 := by
    rw [hden]
    exact Complex.ofReal_ne_zero.mpr hd.ne'
  have h := homogeneousHorner_positive ell b Z t hb hZ ht U V J hcert
  rw [homogeneousHorner_eval U V J _ _ hden0, hn, hden] at h
  have hlen : (evenValues ell b Z).length - 1 = 15 := by simp [evenValues]
  rw [hlen, ← Complex.ofReal_div, ← Complex.ofReal_pow] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact pos_of_mul_pos_right h (pow_nonneg hd.le 15)

/-- The entire parameter box, including repeated coherent occurrences of b,Z,
has strictly positive determinant at every real frequency. -/
theorem rawDeterminant_positive (ell : Fin 4) (b Z v : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2) :
    0 < ((rawDeterminant ell b Z).eval (v : ℂ)).re := by
  rw [rawDeterminant_eval_square]
  rcases nonnegative_chart_cover (v ^ 2) (sq_nonneg v) with h | h | h
  · obtain ⟨t, ht, he⟩ := h
    rw [he]
    simpa using chart_value_positive ell b Z t hb hZ ht 0 1 1
      (by norm_num; linarith) (certificate_first ell)
  · obtain ⟨t, ht, he⟩ := h
    rw [he]
    simpa using chart_value_positive ell b Z t hb hZ ht 1 10 1
      (by norm_num; linarith) (certificate_second ell)
  · obtain ⟨t, ht, he⟩ := h
    rw [he]
    simpa using chart_value_positive ell b Z t hb hZ ht 10 1 0
      (by norm_num) (certificate_third ell)

end DefocusingNLS.BoundaryCertificate

end OAI
