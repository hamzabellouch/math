import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedRieszRectangle
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszResidueTruncation

namespace OAI

/-! # Character Riesz bounds retaining the exact rectangle residue -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem character_logDeriv_right_continuous (χ : PrimitiveComplexCharacter)
    (b : ℝ) (hb : 1 < b) :
    Continuous (fun t : ℝ => -logDeriv χ.L (rieszMellinLine b t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn := χ.L_ne_zero_one_le_re (rieszMellinLine b t) (by simpa using hb.le)
  exact (((χ.L_analytic _).deriv.div (χ.L_analytic _) hn).neg.continuousAt).comp
    (rieszMellinLine_continuous b).continuousAt

theorem characterRieszMean_residue_rectangle_bound : ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (X a b T M : ℝ) (v : ℂ),
      1 ≤ X → 1 / 2 ≤ a → a ≤ b → 1 < b → b ≤ 2 → 0 < T → 0 ≤ M →
      rectangleBoundaryIntegral (fun s => -logDeriv χ.L s * rieszContourWeight X s)
        a b (-T) T = I * (((2 * Real.pi : ℝ) : ℂ) * v) →
      (∀ s : ℂ, ((s.re = a ∧ |s.im| ≤ T) ∨
        (a ≤ s.re ∧ s.re ≤ b ∧ |s.im| = T)) → ‖logDeriv χ.L s‖ ≤ M) →
      ‖characterRieszMean χ X - v‖ ≤ K * M * X ^ a +
        2 * (M * X ^ b / T ^ 2) * (b - a) +
        2 * (1 / (b - 1) + C) * X ^ b / T := by
  obtain ⟨K, hK, hleft⟩ := weightedRiesz_left_segment_bound
  obtain ⟨C, hC, hright⟩ := character_logDeriv_right_pole_bound
  refine ⟨K, C, hK, hC, ?_⟩
  intro χ X a b T M v hX ha hab hb hb2 hT hM hres hedge
  have hXp : 0 < X := by linarith
  have hlow (t : ℝ) (ht : t ∈ Icc (-T) T) :
      ‖-logDeriv χ.L (rieszMellinLine a t)‖ ≤ M := by
    rw [norm_neg]
    apply hedge
    left
    exact ⟨rieszMellinLine_re _ _, by simpa [rieszMellinLine] using abs_le.mpr ht⟩
  have he (σ t : ℝ) (hσ : σ ∈ Icc a b) (ht : |t| = T) :
      ‖-logDeriv χ.L ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M := by
    rw [norm_neg]
    apply hedge
    right
    simpa using And.intro hσ.1 (And.intro hσ.2 ht)
  have hl := hleft (fun s => -logDeriv χ.L s) X a T M hXp ha hM hlow
  have hl' : ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ ≤ K * M * X ^ a := by
    simpa only [intervalIntegral.integral_of_le (show -T ≤ T by linarith),
      integral_Icc_eq_integral_Ioc, rightRieszIntegrand] using hl
  have hu := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv χ.L s)
    X a b T M hX hab (by simpa [abs_of_pos hT]) hM
    (fun σ hσ => he σ T hσ (abs_of_pos hT))
  have hd := weightedRiesz_horizontal_segment_bound (fun s => -logDeriv χ.L s)
    X a b (-T) M hX hab (by simpa [abs_neg, abs_of_pos hT]) hM
    (fun σ hσ => he σ (-T) hσ (by rw [abs_neg, abs_of_pos hT]))
  rw [neg_sq] at hd
  have hv := rectangle_vertical_shift_residue_norm_bound _ a b (-T) T _ hres
  have hrightBound (t : ℝ) : ‖-logDeriv χ.L (rieszMellinLine b t)‖ ≤ 1 / (b - 1) + C := by
    simpa only [norm_neg, rieszMellinLine_re] using hright χ (rieszMellinLine b t)
      (by simpa using hb) (by simpa using hb2)
  have ht := riesz_residue_truncation (fun s => -logDeriv χ.L s) X b
    (1 / (b - 1) + C) T v hXp hb.le (by positivity) hT
    (character_logDeriv_right_continuous χ b hb) hrightBound
  rw [← characterRieszMean_eq_vertical_logDerivative χ X b hXp hb] at ht
  change ‖(∫ t in -T..T, rightRieszIntegrand χ X b t) - _‖ ≤
    ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ + _ + _ at hv
  change ‖characterRieszMean χ X - v‖ ≤
    ‖(∫ t in -T..T, rightRieszIntegrand χ X b t) - ((2 * Real.pi : ℝ) : ℂ) * v‖ + _ at ht
  change ‖∫ σ in a..b, -logDeriv χ.L ((σ : ℂ) + (T : ℂ) * I) *
    rieszContourWeight X ((σ : ℂ) + (T : ℂ) * I)‖ ≤ _ at hu
  change ‖∫ σ in a..b, -logDeriv χ.L ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) *
    rieszContourWeight X ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ _ at hd
  change ‖∫ t in -T..T, rightRieszIntegrand χ X a t‖ ≤ _ at hl'
  nlinarith

end Ostmann

end OAI
