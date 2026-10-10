import OAI.Analysis.KadisonKastler.RegularFourierTransport
import OAI.Analysis.KadisonKastler.RegularCoreDensePeriods
import OAI.Analysis.KadisonKastler.ModularSpectralPhase

namespace OAI

/-! # Continuous character fields in the scalar spectral variable -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularCharacter_apply_eq_fourier_translate (a : ℝ) (f : RegularCoreHilbert H) :
    (regularCharacterUnitary (H := H) a : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f =
      (Lp.fourierTransformₗᵢ ℝ H).symm (regularTranslateApply (-(a / (2 * Real.pi))) (𝓕 f)) := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  have ha : 2 * Real.pi * (a / (2 * Real.pi)) = a := by field_simp
  have h := fourier_regularCharacterUnitary (a / (2 * Real.pi)) f
  change (Lp.fourierTransformₗᵢ ℝ H) ((regularCharacterUnitary (H := H)
    (2 * Real.pi * (a / (2 * Real.pi))) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) = _ at h
  rwa [ha] at h

theorem continuous_regularCharacterUnitary (f : RegularCoreHilbert H) :
    Continuous (fun a : ℝ => (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) := by
  simp_rw [regularCharacter_apply_eq_fourier_translate]
  exact (Lp.fourierTransformₗᵢ ℝ H).symm.continuous.comp
    ((continuous_regularTranslateApply (𝓕 f)).comp (by fun_prop))

def resolventLogFrequency (s : ℝ) : ℝ := Real.log (1 - s) - Real.log s

theorem resolventLogFrequency_measurable : Measurable resolventLogFrequency :=
  (Real.measurable_log.comp (measurable_const.sub measurable_id)).sub Real.measurable_log

theorem modularSpectralPhase_eq_character (s t : ℝ) :
    modularSpectralPhase t s = regularCharacterScalar (resolventLogFrequency s) t := by
  change Complex.exp (Complex.I * ((t : ℂ) * (resolventLogFrequency s : ℂ))) =
    Complex.exp (((resolventLogFrequency s * t : ℝ) : ℂ) * Complex.I)
  rw [Complex.ofReal_mul]
  congr 1
  ring

end

end KadisonKastler

end OAI
