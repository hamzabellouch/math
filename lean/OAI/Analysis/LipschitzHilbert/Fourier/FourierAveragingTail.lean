import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingMeasure

namespace OAI

/-!
# Quantitative tails of the averaging kernel

The Fourier-square kernel has a finite second moment, proved directly from
its Schwartz seminorms. This gives the polynomial tail estimate used in the
near-uniform interval convolution, with a constant from a fixed kernel.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem fourierSquare_second_moment_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun t => t ^ 2 * fourierSquare h t) := by
  have hbound (t : ℝ) : t ^ 2 * fourierSquare h t ≤
      SchwartzMap.seminorm ℝ 2 0 (𝓕 h) * ‖𝓕 h t‖ := by
    have hb := mul_le_mul_of_nonneg_right
      (SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 h) 2 t) (norm_nonneg (𝓕 h t))
    rw [Real.norm_eq_abs, sq_abs] at hb
    simpa only [fourierSquare, mul_assoc, pow_two] using hb
  exact ((𝓕 h).integrable.norm.const_mul _).mono'
    ((continuous_id.pow 2).mul (fourierSquare_continuous h)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg t) (fourierSquare_nonneg h t))] using hbound t)

theorem fourierAveraging_second_moment_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => t ^ 2) (fourierAveragingMeasure h) := by
  unfold fourierAveragingMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (fourierAveragingDensity_continuous h).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (fourierAveragingDensity_nonneg h _), smul_eq_mul]
  convert (fourierSquare_second_moment_integrable h).div_const
    (∫ x, fourierSquare h x) using 1
  funext t
  unfold fourierAveragingDensity
  ring

theorem fourierAveraging_second_moment_nonneg (h : SchwartzMap ℝ ℂ) :
    0 ≤ ∫ t : ℝ, t ^ 2 ∂fourierAveragingMeasure h :=
  integral_nonneg fun _ => sq_nonneg _

/-- The tail outside a central interval is controlled by the second moment. -/
theorem probability_central_mass_of_second_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hint : Integrable (fun t : ℝ => t ^ 2) μ)
    {R : ℝ} (hR : 0 < R) :
    1 - (∫ t : ℝ, t ^ 2 ∂μ) / R ^ 2 ≤ μ.real (Set.Icc (-R) R) := by
  let A : Set ℝ := Set.Icc (-R) R
  have hA : MeasurableSet A := measurableSet_Icc
  have htail := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun t : ℝ => sq_nonneg t) hint (R ^ 2)
  have hsub : Aᶜ ⊆ {t : ℝ | R ^ 2 ≤ t ^ 2} := by
    intro t ht
    have hnot : ¬(-R ≤ t ∧ t ≤ R) := ht
    rcases not_and_or.mp hnot with hleft | hright
    · have hlt : t < -R := lt_of_not_ge hleft
      have hh := mul_nonneg (show 0 ≤ -t - R by linarith) (show 0 ≤ -t + R by linarith)
      exact show R ^ 2 ≤ t ^ 2 by nlinarith [hh]
    · have hlt : R < t := lt_of_not_ge hright
      have hh := mul_nonneg (show 0 ≤ t - R by linarith) (show 0 ≤ t + R by linarith)
      exact show R ^ 2 ≤ t ^ 2 by nlinarith [hh]
  have hmono : μ.real Aᶜ ≤ μ.real {t : ℝ | R ^ 2 ≤ t ^ 2} :=
    measureReal_mono hsub
  have hcomp : μ.real Aᶜ = 1 - μ.real A := by
    rw [measureReal_compl hA, probReal_univ]
  rw [hcomp] at hmono
  have hdiv : μ.real {t : ℝ | R ^ 2 ≤ t ^ 2} ≤
      (∫ t : ℝ, t ^ 2 ∂μ) / R ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hR)).2 (by nlinarith [htail])
  dsimp only [A] at hmono
  linarith

/-- Dilation changes the Fourier gap by the reciprocal physical scale. -/
theorem fourierGap_map_dilation (μ : Measure ℝ) [IsFiniteMeasure μ]
    {gap scale : ℝ} (hscale : 0 < scale) (hgap : PhaseCombinatorics.FourierGap μ gap) :
    PhaseCombinatorics.FourierGap (μ.map (fun t => scale * t)) (gap / scale) := by
  intro s hs
  unfold PhaseCombinatorics.fourierMoment
  rw [integral_map (by fun_prop) (PhaseCombinatorics.continuous_character s).aestronglyMeasurable]
  have hchar (t : ℝ) : PhaseCombinatorics.character s (scale * t) =
      PhaseCombinatorics.character (scale * s) t := by
    unfold PhaseCombinatorics.character
    have heq : s * (scale * t) = scale * s * t := by ring
    rw [heq]
  simp only [hchar]
  apply hgap
  rw [abs_mul, abs_of_pos hscale]
  have h := (div_le_iff₀ hscale).1 (show gap / 4 / scale ≤ |s| by
    convert hs using 1
    ring)
  nlinarith

theorem second_moment_map_dilation (μ : Measure ℝ) [IsFiniteMeasure μ] (scale : ℝ) :
    (∫ t : ℝ, t ^ 2 ∂μ.map (fun t => scale * t)) =
      scale ^ 2 * ∫ t : ℝ, t ^ 2 ∂μ := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  exact integral_const_mul _ _

end LipschitzHilbert

end

end OAI
