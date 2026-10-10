import OAI.Analysis.KadisonKastler.CoreTraceScalarGauge

namespace OAI

/-! # Dual-character covariance of bounded frequency windows -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyWindow_character_intertwine (a b s : ℝ) :
    regularFrequencyWindow (H := H) (a + s) (b + s) *
        (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (2 * Real.pi * s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
          regularFrequencyWindow a b := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularFrequencyWindow (a + s) (b + s)
    ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) : RegularCoreHilbert H) =
    𝓕 ((regularCharacterUnitary (H := H) (2 * Real.pi * s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularFrequencyWindow a b f))
  rw [fourier_frequencyWindow, fourier_regularCharacterUnitary,
    fourier_regularCharacterUnitary, fourier_frequencyWindow]
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioc (a + s) (b + s))
      measurableSet_Ioc (regularTranslateApply (-s) (𝓕 f : RegularCoreHilbert H)),
    regularTranslateApply_ae (-s) (𝓕 f : RegularCoreHilbert H),
    regularTranslateApply_ae (-s)
      (regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc
        (𝓕 f : RegularCoreHilbert H)),
    (measurePreserving_add_right (volume : Measure ℝ) (-s)).quasiMeasurePreserving.ae_eq_comp
      (regularIndicatorProjection_apply_ae (Set.Ioc a b) measurableSet_Ioc
        (𝓕 f : RegularCoreHilbert H))] with t hp ht hr hq
  simp only [Function.comp_def] at hq
  rw [hp, hr, hq]
  have he : t ∈ Set.Ioc (a + s) (b + s) ↔ t + -s ∈ Set.Ioc a b := by
    simp only [Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases h : t ∈ Set.Ioc (a + s) (b + s)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (he.mp h)]
    exact ht
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt he.mpr h)]

theorem regularFrequencyWindow_character_conj (a b s : ℝ) :
    unitaryConj (regularCharacterUnitary (H := H) (2 * Real.pi * s))
      (regularFrequencyWindow a b) = regularFrequencyWindow (a + s) (b + s) := by
  unfold unitaryConj
  rw [← regularFrequencyWindow_character_intertwine, mul_assoc,
    Unitary.mul_star_self_of_mem (regularCharacterUnitary (H := H) (2 * Real.pi * s)).property,
    mul_one]

end

end KadisonKastler

end OAI
