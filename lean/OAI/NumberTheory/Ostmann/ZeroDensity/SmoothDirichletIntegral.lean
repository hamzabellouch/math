import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothVerticalKernel

namespace OAI

/-! # The initial vertical-line formula for the smooth Mangoldt sum -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

noncomputable def characterVerticalTerm (χ : PrimitiveComplexCharacter) (X : ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (characterMangoldtCoefficient χ) (primeMellinLine t) n * primeVerticalWeight X t

theorem characterVerticalTerm_norm (χ : PrimitiveComplexCharacter) (X : ℝ) (n : ℕ) (t : ℝ) :
    ‖characterVerticalTerm χ X n t‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) 2 n‖ * ‖primeVerticalWeight X t‖ := by
  rw [characterVerticalTerm, norm_mul, characterMangoldt_term_norm]

theorem characterVerticalTerm_integrable (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (n : ℕ) : Integrable (characterVerticalTerm χ X n) := by
  apply ((primeVerticalWeight_integrable X hX).norm.const_mul
    ‖LSeries.term (characterMangoldtCoefficient χ) 2 n‖).mono'
  · exact ((characterMangoldt_term_continuous χ n).mul
      (primeVerticalWeight_continuous X hX)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => (characterVerticalTerm_norm χ X n t).le)

theorem characterVerticalTerm_summable_norm (χ : PrimitiveComplexCharacter)
    (X : ℝ) :
    Summable (fun n => ∫ t : ℝ, ‖characterVerticalTerm χ X n t‖) := by
  have hs := (characterMangoldtCoefficient_summable χ).norm.mul_right
    (∫ t : ℝ, ‖primeVerticalWeight X t‖)
  apply hs.congr
  intro n
  simp only [characterVerticalTerm_norm, integral_const_mul]

theorem smoothMangoldtMean_eq_vertical_LSeries (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean χ.modulus χ.character X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        LSeries (characterMangoldtCoefficient χ) (primeMellinLine t) * primeVerticalWeight X t := by
  calc
    _ = ∑' n : ℕ, characterMangoldtCoefficient χ n * (primeMeanTest (n / X) : ℂ) := by
      apply tsum_congr
      intro n
      simp only [characterMangoldtCoefficient]
      ring
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, characterVerticalTerm χ X n t :=
      tsum_congr (fun n => (characterMangoldt_term_inversion χ X hX n).symm)
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' n : ℕ, ∫ t : ℝ, characterVerticalTerm χ X n t := tsum_mul_left
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑' n : ℕ, characterVerticalTerm χ X n t := by
      rw [integral_tsum_of_summable_integral_norm
        (characterVerticalTerm_integrable χ X hX) (characterVerticalTerm_summable_norm χ X)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact tsum_mul_right

theorem PrimitiveComplexCharacter.mangoldt_LSeries_eq (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (characterMangoldtCoefficient χ) s = -deriv χ.L s / χ.L s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  change LSeries (characterMangoldtCoefficient χ) s =
    -deriv (DirichletCharacter.LFunction χ.character) s / DirichletCharacter.LFunction χ.character s
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ.character hs,
    DirichletCharacter.LFunction_eq_LSeries χ.character hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ.character hs

/-- The exact starting contour for the published explicit formula. -/
theorem smoothMangoldtMean_eq_vertical_logDerivative (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) :
    smoothMangoldtMean χ.modulus χ.character X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (-deriv χ.L (primeMellinLine t) / χ.L (primeMellinLine t)) *
          primeVerticalWeight X t := by
  rw [smoothMangoldtMean_eq_vertical_LSeries χ X hX]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [χ.mangoldt_LSeries_eq (primeMellinLine t) (by simp)]

end Ostmann

end OAI
