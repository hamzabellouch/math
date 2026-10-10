import OAI.NumberTheory.Ostmann.ZeroDensity.RieszNegativeTail
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszHorizontalEstimate
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterContourZeros

namespace OAI

/-! # The exact finite-rectangle truncation of the Riesz integral -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem rightRieszIntegrand_integrable (χ : PrimitiveComplexCharacter)
    (X b : ℝ) (hX : 0 < X) (hb : 1 < b) (hb2 : b ≤ 2) :
    Integrable (rightRieszIntegrand χ X b) := by
  obtain ⟨C, hC, hbound⟩ := character_logDeriv_right_pole_bound
  have hcL : Continuous χ.L := continuous_iff_continuousAt.mpr
    (fun s => (χ.L_analytic s).continuousAt)
  have hcD : Continuous (deriv χ.L) := continuous_iff_continuousAt.mpr
    (fun s => (χ.L_analytic s).deriv.continuousAt)
  have hn (t : ℝ) : χ.L (rieszMellinLine b t) ≠ 0 :=
    χ.L_ne_zero_one_le_re _ (by simpa using hb.le)
  have hcont : Continuous (rightRieszIntegrand χ X b) := by
    change Continuous (fun t => -(deriv χ.L (rieszMellinLine b t) /
      χ.L (rieszMellinLine b t)) * rieszVerticalWeight X b t)
    exact ((hcD.comp (rieszMellinLine_continuous b)).div
      (hcL.comp (rieszMellinLine_continuous b)) hn).neg.mul
      (rieszVerticalWeight_continuous X b hX (by linarith))
  apply ((rieszVerticalWeight_integrable X b hX hb.le).norm.const_mul
    (1 / (b - 1) + C)).mono' hcont.aestronglyMeasurable
  filter_upwards with t
  rw [rightRieszIntegrand, norm_mul, norm_neg]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [rieszMellinLine_re] using hbound χ (rieszMellinLine b t)
    (by simpa using hb) (by simpa using hb2)

theorem integral_three_parts (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) :
    (∫ t : ℝ, f t) = (∫ t in Iic (-T), f t) + (∫ t in -T..T, f t) +
      (∫ t in Ioi T, f t) := by
  have hfull := intervalIntegral.integral_Iic_add_Ioi (b := T) hf.integrableOn hf.integrableOn
  have hseg := intervalIntegral.integral_Iic_sub_Iic (a := -T) (b := T)
    hf.integrableOn hf.integrableOn
  linear_combination hseg - hfull

theorem characterRieszMean_truncation : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (X b T : ℝ), 0 < X → 1 < b → b ≤ 2 → 0 < T →
      ‖characterRieszMean χ X‖ ≤
        ‖∫ t in -T..T, rightRieszIntegrand χ X b t‖ +
          2 * (1 / (b - 1) + C) * X ^ b / T := by
  obtain ⟨C1, hC1, hpos⟩ := rightRieszIntegrand_tail
  obtain ⟨C2, hC2, hneg⟩ := rightRieszIntegrand_negative_tail
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro χ X b T hX hb hb2 hT
  have hp := hpos χ X b T hX hb hb2 hT
  have hn := hneg χ X b T hX hb hb2 hT
  have hf := rightRieszIntegrand_integrable χ X b hX hb hb2
  have hnorm : ‖characterRieszMean χ X‖ ≤ ‖∫ t : ℝ, rightRieszIntegrand χ X b t‖ := by
    rw [characterRieszMean_eq_vertical_logDerivative χ X b hX hb, norm_mul]
    have hc : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [Real.pi_gt_three])
    exact mul_le_of_le_one_left (norm_nonneg _) hc
  have hsum : ‖∫ t : ℝ, rightRieszIntegrand χ X b t‖ ≤
      ‖∫ t in Iic (-T), rightRieszIntegrand χ X b t‖ +
      ‖∫ t in -T..T, rightRieszIntegrand χ X b t‖ +
      ‖∫ t in Ioi T, rightRieszIntegrand χ X b t‖ := by
    rw [integral_three_parts _ hf T]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hbase : 0 ≤ X ^ b / T := div_nonneg (Real.rpow_nonneg hX.le _) hT.le
  have hslack := mul_nonneg (show 0 ≤ C1 + C2 by positivity) hbase
  calc
    _ ≤ ‖∫ t in Iic (-T), rightRieszIntegrand χ X b t‖ +
        ‖∫ t in -T..T, rightRieszIntegrand χ X b t‖ +
        ‖∫ t in Ioi T, rightRieszIntegrand χ X b t‖ := hnorm.trans hsum
    _ ≤ ((1 / (b - 1) + C2) * X ^ b / T) +
        ‖∫ t in -T..T, rightRieszIntegrand χ X b t‖ +
        ((1 / (b - 1) + C1) * X ^ b / T) :=
      add_le_add (add_le_add hn le_rfl) hp
    _ ≤ _ := by
      apply sub_nonneg.mp
      convert hslack using 1
      ring

end Ostmann

end OAI
