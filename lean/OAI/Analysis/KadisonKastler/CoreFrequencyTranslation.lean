import OAI.Analysis.KadisonKastler.CoreTraceScalarGauge

namespace OAI

/-! # Translation invariance of a bounded core frequency window -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyWindow_commute_translation (a b : ℝ) (s : Multiplicative ℝ) :
    Commute (regularFrequencyWindow (H := H) a b)
      (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularFrequencyWindow a b (regularTranslateApply s.toAdd f)) :
    RegularCoreHilbert H) = 𝓕 (regularTranslateApply s.toAdd (regularFrequencyWindow a b f))
  rw [fourier_frequencyWindow, fourier_regularTranslateApply,
    fourier_regularTranslateApply, fourier_frequencyWindow]
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioc a b) measurableSet_Ioc
      ((regularCharacterUnitary (H := H) (2 * Real.pi * s.toAdd) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (𝓕 f)),
    regularCharacterUnitary_apply_ae (2 * Real.pi * s.toAdd) (𝓕 f : RegularCoreHilbert H),
    regularCharacterUnitary_apply_ae (2 * Real.pi * s.toAdd)
      (regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc (𝓕 f : RegularCoreHilbert H)),
    regularIndicatorProjection_apply_ae (Set.Ioc a b) measurableSet_Ioc (𝓕 f : RegularCoreHilbert H)]
    with t hp hc hd hq
  rw [hp, hd, hq]
  by_cases ht : t ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hc]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]

end

end KadisonKastler

end OAI
