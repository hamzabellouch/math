import OAI.NumberTheory.Ostmann.ZeroDensity.RieszVerticalWeight
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothDirichletIntegral

namespace OAI

/-! # The exact starting contour for the integrated Chebyshev sum -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

noncomputable def characterRieszMean (χ : PrimitiveComplexCharacter) (X : ℝ) : ℂ :=
  ∑' n : ℕ, characterMangoldtCoefficient χ n * rieszPrimeTest (n / X)

noncomputable def characterRieszVerticalTerm (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (characterMangoldtCoefficient χ) (rieszMellinLine σ t) n *
    rieszVerticalWeight X σ t

theorem characterRieszVerticalTerm_norm (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (n : ℕ) (t : ℝ) :
    ‖characterRieszVerticalTerm χ X σ n t‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) (σ : ℂ) n‖ *
        ‖rieszVerticalWeight X σ t‖ := by
  rw [characterRieszVerticalTerm, norm_mul, characterMangoldt_riesz_term_norm]

theorem characterRieszVerticalTerm_integrable (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    Integrable (characterRieszVerticalTerm χ X σ n) := by
  apply ((rieszVerticalWeight_integrable X σ hX hσ).norm.const_mul
    ‖LSeries.term (characterMangoldtCoefficient χ) (σ : ℂ) n‖).mono'
  · exact ((characterMangoldt_riesz_term_continuous χ σ n).mul
      (rieszVerticalWeight_continuous X σ hX (by linarith))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => (characterRieszVerticalTerm_norm χ X σ n t).le)

theorem characterRieszVerticalTerm_summable_norm (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n => ∫ t : ℝ, ‖characterRieszVerticalTerm χ X σ n t‖) := by
  have hsum : LSeriesSummable (characterMangoldtCoefficient χ) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by simpa using hσ)
  have hs := hsum.norm.mul_right (∫ t : ℝ, ‖rieszVerticalWeight X σ t‖)
  apply hs.congr
  intro n
  simp only [characterRieszVerticalTerm_norm, integral_const_mul]

theorem characterMangoldt_riesz_term_inversion (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, characterRieszVerticalTerm χ X σ n t) =
      characterMangoldtCoefficient χ n * rieszPrimeTest (n / X) := by
  by_cases hn : n = 0
  · subst n
    simp [characterRieszVerticalTerm, characterMangoldtCoefficient]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkernel (t : ℝ) : characterRieszVerticalTerm χ X σ n t =
      characterMangoldtCoefficient χ n *
        (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
          rieszMellinKernel (rieszMellinLine σ t) := by
    rw [characterRieszVerticalTerm, LSeries.term_of_ne_zero hn, rieszVerticalWeight,
      Complex.cpow_neg, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hnR.le hX.le, inv_div]
    push_cast
    ring
  simp_rw [hkernel, mul_assoc]
  rw [integral_const_mul]
  have hinv := rieszPrimeTest_mellin_inversion σ ((n : ℝ) / X) hσ (div_pos hnR hX)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
      rieszMellinKernel (rieszMellinLine σ t)) = _ at hinv
  rw [← hinv]
  ring

theorem characterRieszMean_eq_vertical_logDerivative (χ : PrimitiveComplexCharacter)
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 < σ) :
    characterRieszMean χ X =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
        (-logDeriv χ.L (rieszMellinLine σ t)) * rieszVerticalWeight X σ t := by
  unfold characterRieszMean
  calc
    _ = ∑' n : ℕ, ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, characterRieszVerticalTerm χ X σ n t :=
      tsum_congr (fun n => (characterMangoldt_riesz_term_inversion χ X σ hX hσ.le n).symm)
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∑' n : ℕ, ∫ t : ℝ, characterRieszVerticalTerm χ X σ n t := tsum_mul_left
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑' n : ℕ, characterRieszVerticalTerm χ X σ n t := by
      rw [integral_tsum_of_summable_integral_norm
        (characterRieszVerticalTerm_integrable χ X σ hX hσ.le)
        (characterRieszVerticalTerm_summable_norm χ X σ hσ)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [show (∑' n : ℕ, characterRieszVerticalTerm χ X σ n t) =
        LSeries (characterMangoldtCoefficient χ) (rieszMellinLine σ t) * rieszVerticalWeight X σ t from tsum_mul_right]
      rw [χ.mangoldt_LSeries_eq _ (by simpa using hσ)]
      simp only [logDeriv_apply, neg_div]

end Ostmann

end OAI
