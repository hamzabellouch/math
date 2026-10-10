import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingConvolution
import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingTail

namespace OAI

/-!
# Near-uniform Fourier-supported averaging

The averaging probability in §9 is the convolution of the uniform law on
an expanded interval with a dilated, fixed Fourier-square probability.
Its explicit loss is expansion/length plus a second-moment tail.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace LipschitzHilbert

open PhaseCombinatorics

theorem interval_convolution_minorization (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b pad η : ℝ} (hab : a < b) (hpad : 0 ≤ pad)
    (hmass : 1 - η ≤ μ.real (Set.Icc (-pad) pad) *
      ((b - a) / (b - a + 2 * pad))) :
    ENNReal.ofReal (1 - η) • intervalProbability a b ≤
      intervalProbability (a - pad) (b + pad) ∗ μ := by
  have : IsProbabilityMeasure (intervalProbability (a - pad) (b + pad)) :=
    intervalProbability_isProbability (by linarith)
  have hminor := convolution_minorization
    (intervalProbability (a - pad) (b + pad)) μ (intervalProbability a b)
    measurableSet_Icc (fun y hy => intervalProbability_le_translated hab hpad (abs_le.mpr hy))
  have hcoeff : ENNReal.ofReal (1 - η) ≤ μ (Set.Icc (-pad) pad) *
      ENNReal.ofReal ((b - a) / (b - a + 2 * pad)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), ← measureReal_def,
      ← ENNReal.ofReal_mul measureReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hmass
  refine le_trans ?_ hminor
  apply Measure.le_iff.2
  intro A _
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr

theorem expansion_tail_loss {H pad tail mass : ℝ}
    (hH : 0 < H) (hpad : 0 ≤ pad) (htail : 0 ≤ tail) (hmass : 1 - tail ≤ mass) :
    1 - (2 * pad / H + tail) ≤ mass * (H / (H + 2 * pad)) := by
  have hlarge : 0 < H + 2 * pad := by positivity
  have hratio : 0 ≤ H / (H + 2 * pad) := by positivity
  have hm := mul_le_mul_of_nonneg_right hmass hratio
  have hlower : 1 - (2 * pad / H + tail) ≤
      (1 - tail) * (H / (H + 2 * pad)) := by
    have heq : (1 - tail) * (H / (H + 2 * pad)) - (1 - (2 * pad / H + tail)) =
        (2 * pad * (2 * pad + H * tail)) / (H * (H + 2 * pad)) := by
      field_simp
      ring
    have hnonneg : 0 ≤ (2 * pad * (2 * pad + H * tail)) / (H * (H + 2 * pad)) := by
      positivity
    rw [← heq] at hnonneg
    linarith
  exact hlower.trans hm

/-- Explicit near-uniform probability and exact remainder. The only input
about the base kernel is its proved probability, Fourier gap, and moment. -/
theorem interval_fourier_mixture (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun t : ℝ => t ^ 2) μ)
    {a b pad scale gap : ℝ} (hab : a < b) (hpad : 0 < pad) (hscale : 0 < scale)
    (hgap : FourierGap μ gap)
    (hsmall : 2 * pad / (b - a) +
      scale ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / pad ^ 2 < 1) :
    let η := 2 * pad / (b - a) + scale ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / pad ^ 2
    0 < η ∧ η < 1 ∧ ∃ τ : Measure ℝ, IsProbabilityMeasure τ ∧
      predictionMixture (intervalProbability a b) τ η =
        intervalProbability (a - pad) (b + pad) ∗ μ.map (fun t => scale * t) ∧
      FourierGap (predictionMixture (intervalProbability a b) τ η) (gap / scale) := by
  dsimp only
  let η := 2 * pad / (b - a) + scale ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / pad ^ 2
  have hH : 0 < b - a := sub_pos.mpr hab
  have hmoment0 : 0 ≤ ∫ t : ℝ, t ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hη0 : 0 < η := by dsimp [η]; positivity
  have : IsProbabilityMeasure (intervalProbability a b) := intervalProbability_isProbability hab
  have : IsProbabilityMeasure (intervalProbability (a - pad) (b + pad)) :=
    intervalProbability_isProbability (by linarith)
  have hint : Integrable (fun t : ℝ => t ^ 2) (μ.map (fun t => scale * t)) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    simpa only [Function.comp_def, mul_pow] using hmoment.const_mul (scale ^ 2)
  have hmass := probability_central_mass_of_second_moment
    (μ.map (fun t => scale * t)) hint hpad
  rw [second_moment_map_dilation] at hmass
  have hminor := interval_convolution_minorization (μ.map (fun t => scale * t)) hab hpad.le
    (expansion_tail_loss hH hpad.le (by positivity) hmass)
  obtain ⟨τ, hτ, hmix⟩ := probability_mixture_of_minorization
    (intervalProbability (a - pad) (b + pad) ∗ μ.map (fun t => scale * t))
    (intervalProbability a b) hη0 hsmall hminor
  refine ⟨hη0, hsmall, τ, hτ, hmix, ?_⟩
  rw [hmix, Measure.conv_comm]
  exact fourierGap_conv_left _ _ (fourierGap_map_dilation μ hscale hgap)

/-- A fixed actual Schwartz-square kernel suffices for all interval lengths
and dilation parameters. Its second moment is a single finite constant. -/
theorem exists_fixed_fourier_averaging_kernel :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ FourierGap μ 1 ∧
      Integrable (fun t : ℝ => t ^ 2) μ := by
  obtain ⟨h, hh, hprob, hgap⟩ := exists_fourierAveragingMeasure (by norm_num : 0 < (1 : ℝ))
  exact ⟨fourierAveragingMeasure h, hprob, hgap, fourierAveraging_second_moment_integrable h⟩

end LipschitzHilbert

end

end OAI
