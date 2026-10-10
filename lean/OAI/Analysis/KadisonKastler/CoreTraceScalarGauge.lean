import OAI.Analysis.KadisonKastler.CoreTraceScalarBalance

namespace OAI

/-! # Trace balance between the two scalar gauge actions -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_frequencyWindow (a b : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularFrequencyWindow a b f) : RegularCoreHilbert H) =
      regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc (𝓕 f) := by
  unfold regularFrequencyWindow
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  exact (Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply _

theorem fourier_character_apply (l : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 ((regularCharacterUnitary (H := H) l :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) : RegularCoreHilbert H) =
      regularTranslateApply (-(l / (2 * Real.pi))) (𝓕 f) := by
  rw [regularCharacter_apply_eq_fourier_translate]
  exact (Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply _

theorem fourier_character_star_apply (l : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 ((star (regularCharacterUnitary (H := H) l) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) : RegularCoreHilbert H) =
      regularTranslateApply (l / (2 * Real.pi)) (𝓕 f) := by
  have he : (star (regularCharacterUnitary (H := H) l) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCharacterUnitary (H := H) (-l) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    congrArg Subtype.val (regularGroup_star_eq (regularCharacterRepresentation (H := H)) l)
  rw [he, fourier_character_apply]
  simp only [neg_div, neg_neg]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem coreTrace_scalarGauge_balance {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (Real.sqrt s : ℂ) •
      regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
          ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar)) =
    (Real.sqrt (1-s) : ℂ) •
      (star (regularCharacterUnitary (H := ℂ) (resolventLogFrequency s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (resolventLogFrequency s) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
            ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar))) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  simp only [map_smul]
  change (Real.sqrt s : ℂ) • (𝓕 (_ : RegularCoreHilbert ℂ)) =
    (Real.sqrt (1-s) : ℂ) • (𝓕 (_ : RegularCoreHilbert ℂ))
  have hf : (𝓕 ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar) :
      RegularCoreHilbert ℂ) = coreTraceFrequencyScalar :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply _
  rw [fourier_frequencyWindow, fourier_character_star_apply, hf,
    fourier_character_star_apply, fourier_frequencyWindow, fourier_character_apply, hf]
  exact coreTraceFrequencyScalar_spectral_balance hs hs1

end

end KadisonKastler

end OAI
