import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorSeries
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteSeriesBridge

namespace OAI

/-! # The exact initial contour of the compact Mobius zero detector -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators Classical

noncomputable def densityDetectorVerticalTerm (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (densityDetectorCharacterCoefficient χ X) (s + (2 + (t : ℂ) * I)) n *
    (Y : ℂ) ^ (2 + (t : ℂ) * I) * densityDetectorKernel (2 + (t : ℂ) * I)

 theorem densityDetectorVerticalTerm_norm (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) (t : ℝ) :
    ‖densityDetectorVerticalTerm χ X s Y n t‖ =
      (‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + 2) n‖ * Y ^ 2) *
        ‖densityDetectorKernel (2 + (t : ℂ) * I)‖ := by
  unfold densityDetectorVerticalTerm
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have he : (2 + (t : ℂ) * I).re = (2 : ℝ) := by simp
  rw [he, Real.rpow_two]
  have hn : ‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + (2 + (t : ℂ) * I)) n‖ =
      ‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + 2) n‖ := by
    simp only [LSeries.norm_term_eq]
    congr 2
    simp
  rw [hn]

 theorem densityDetectorVerticalTerm_continuous (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    Continuous (densityDetectorVerticalTerm χ X s Y n) := by
  have hk : Continuous (fun t : ℝ => densityDetectorKernel (2 + (t : ℂ) * I)) := by
    unfold densityDetectorKernel
    apply continuous_const.div (by fun_prop)
    intro t
    apply mul_ne_zero
    · apply mul_ne_zero <;> norm_num [Complex.ext_iff]
    · norm_num [Complex.ext_iff]
  have hpow : Continuous (fun t : ℝ => (Y : ℂ) ^ (2 + (t : ℂ) * I)) :=
    (differentiable_id.const_cpow (Or.inl (by exact_mod_cast hY.ne'))).continuous.comp (by fun_prop)
  apply Continuous.mul _ hk
  apply Continuous.mul _ hpow
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    apply continuous_const.div
    · exact (differentiable_id.const_cpow (Or.inl (by exact_mod_cast hn))).continuous.comp (by fun_prop)
    · intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))

 theorem densityDetectorVerticalTerm_integrable (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    Integrable (densityDetectorVerticalTerm χ X s Y n) := by
  have hk := (densityDetectorKernel_verticalIntegrable 2 (by norm_num)).norm
  apply (hk.const_mul (‖LSeries.term (densityDetectorCharacterCoefficient χ X) (s + 2) n‖ * Y ^ 2)).mono'
    (densityDetectorVerticalTerm_continuous χ X s Y hY n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (densityDetectorVerticalTerm_norm χ X s Y hY n t).le)

 theorem densityDetectorVerticalTerm_summable_norm (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖densityDetectorVerticalTerm χ X s Y n t‖) := by
  have hsum := (densityDetectorCharacterCoefficient_summable χ X (s + 2)
    (by simp; linarith)).norm
  have h := (hsum.mul_right (Y ^ 2)).mul_right
    (∫ t : ℝ, ‖densityDetectorKernel (2 + (t : ℂ) * I)‖)
  apply h.congr
  intro n
  simp only [densityDetectorVerticalTerm_norm χ X s Y hY, integral_const_mul]

 theorem densityDetectorVerticalTerm_inversion (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) (hY : 0 < Y) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, densityDetectorVerticalTerm χ X s Y n t) =
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) := by
  by_cases hn : n = 0
  · subst n
    simp [densityDetectorVerticalTerm]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he (t : ℝ) : densityDetectorVerticalTerm χ X s Y n t =
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n *
        (((n : ℝ) / Y : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I)) *
          densityDetectorKernel (2 + (t : ℂ) * I) := by
    rw [densityDetectorVerticalTerm, density_LSeries_term_add, Complex.cpow_neg,
      Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hnR.le hY.le, inv_div]
    push_cast
    ring
  simp_rw [he, mul_assoc]
  rw [integral_const_mul]
  have hinv := densityDetectorWeight_mellin_inversion 2 ((n : ℝ) / Y) (by norm_num) (div_pos hnR hY)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / Y : ℝ) : ℂ) ^ (-(2 + (t : ℂ) * I)) *
      densityDetectorKernel (2 + (t : ℂ) * I)) = _ at hinv
  rw [← hinv]
  ring

 theorem densityDetectorMean_eq_integral (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (hs : 0 ≤ s.re) (Y : ℝ) (hY : 0 < Y) :
    densityDetectorMean χ X s Y = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
      χ.L (s + (2 + (t : ℂ) * I)) *
        densityMollifier X χ.character (s + (2 + (t : ℂ) * I)) *
          (Y : ℂ) ^ (2 + (t : ℂ) * I) * densityDetectorKernel (2 + (t : ℂ) * I) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [densityDetectorMean_tsum χ X s Y hY]
  simp_rw [← densityDetectorVerticalTerm_inversion χ X s Y hY]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm
    (fun n => densityDetectorVerticalTerm_integrable χ X s Y hY n)
    (densityDetectorVerticalTerm_summable_norm χ X s hs Y hY)]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [densityDetectorVerticalTerm, tsum_mul_right]
  rw [show (∑' n, LSeries.term (densityDetectorCharacterCoefficient χ X)
      (s + (2 + (t : ℂ) * I)) n) =
      χ.L (s + (2 + (t : ℂ) * I)) * densityMollifier X χ.character (s + (2 + (t : ℂ) * I)) from
    density_mollifier_L_product X χ.character _ (by simp; linarith)]

end Ostmann

end OAI
