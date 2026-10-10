import OAI.Analysis.KadisonKastler.FourierReflectedConjugation
import OAI.Analysis.KadisonKastler.CoreTraceScalarGauge

namespace OAI

/-! # Reflected conjugation of the trace packets and frequency window -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularPointwiseConjugation_indicator (J : H ≃ₗᵢ⋆[ℂ] H)
    (s : Set ℝ) (hs : MeasurableSet s) (f : RegularCoreHilbert H) :
    regularPointwiseConjugation J (regularIndicatorProjection s hs f) =
      regularIndicatorProjection s hs (regularPointwiseConjugation J f) := by
  apply Lp.ext
  filter_upwards [regularPointwiseConjugation_apply_ae J (regularIndicatorProjection s hs f),
    regularIndicatorProjection_apply_ae s hs f,
    regularIndicatorProjection_apply_ae s hs (regularPointwiseConjugation J f),
    regularPointwiseConjugation_apply_ae J f] with t hJ hp hq hf
  rw [hJ, hp, hq]
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hf]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, map_zero]

theorem regularReflectedConjugation_frequencyWindow (J : H ≃ₗᵢ⋆[ℂ] H)
    (a b : ℝ) (f : RegularCoreHilbert H) :
    regularReflectedConjugation J (regularFrequencyWindow a b f) =
      regularFrequencyWindow a b (regularReflectedConjugation J f) := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularReflectedConjugation J (regularFrequencyWindow a b f)) :
    RegularCoreHilbert H) = 𝓕 (regularFrequencyWindow a b (regularReflectedConjugation J f))
  rw [fourier_regularReflectedConjugation, fourier_frequencyWindow,
    fourier_frequencyWindow, fourier_regularReflectedConjugation,
    regularPointwiseConjugation_indicator]

theorem regularReflectedConjugation_real_packet (J : H ≃ₗᵢ⋆[ℂ] H)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ∀ᵐ t ∂volume, star (φ t) = φ t) (x : H) :
    regularReflectedConjugation J (regularFrequencyPacket φ x) =
      regularFrequencyPacket φ (J x) := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularReflectedConjugation J (regularFrequencyPacket φ x)) :
    RegularCoreHilbert H) = 𝓕 (regularFrequencyPacket φ (J x))
  rw [fourier_regularReflectedConjugation]
  have hf (y : H) : (𝓕 ((Lp.fourierTransformₗᵢ ℝ H).symm (regularTensorVector φ y)) :
      RegularCoreHilbert H) = regularTensorVector φ y :=
    (Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply _
  simp only [regularFrequencyPacket, hf]
  apply Lp.ext
  filter_upwards [regularPointwiseConjugation_apply_ae J (regularTensorVector φ x),
    regularTensorVector_apply_ae φ x, regularTensorVector_apply_ae φ (J x), hφ]
    with t hJ hx hy hr
  rw [hJ, hx, hy, map_smulₛₗ]
  exact congrArg (fun z : ℂ => z • J x) hr

theorem coreTraceFrequencyScalar_real :
    ∀ᵐ t ∂(volume : Measure ℝ), star (coreTraceFrequencyScalar t) = coreTraceFrequencyScalar t := by
  filter_upwards [coreTraceFrequencyScalar_apply_ae] with t ht
  rw [ht]
  by_cases h : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [coreTraceFrequencyFunction, Set.indicator_of_mem h]
    exact Complex.conj_ofReal _
  · simp only [coreTraceFrequencyFunction, Set.indicator_of_notMem h, star_zero]

end

end KadisonKastler

end OAI
