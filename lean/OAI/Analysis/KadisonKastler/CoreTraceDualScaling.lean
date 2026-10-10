import OAI.Analysis.KadisonKastler.CoreFrequencyCovariance
import OAI.Analysis.KadisonKastler.CoreTraceWeightShift

namespace OAI

/-! # Dual-character rescaling of the supported trace vector

This is the local exponential rescaling needed to distinguish the
semifinite core from a finite or type I factor.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularTranslateApply_tensorVector (a : ℝ)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularTranslateApply a (regularTensorVector φ v) =
      regularTensorVector (regularTranslateApply a φ) v := by
  apply Lp.ext
  filter_upwards [regularTranslateApply_ae a (regularTensorVector φ v),
    (measurePreserving_add_right (volume : Measure ℝ) a).quasiMeasurePreserving.ae_eq_comp
      (regularTensorVector_apply_ae φ v),
    regularTensorVector_apply_ae (regularTranslateApply a φ) v,
    regularTranslateApply_ae a φ] with t ht hv hr hφ
  simp only [Function.comp_def] at hv
  rw [ht, hv, hr, hφ]

theorem regularCharacterStar_frequencyPacket (l : ℝ)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    (star (regularCharacterUnitary (H := H) l) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularFrequencyPacket φ v) =
      regularFrequencyPacket (regularTranslateApply (l / (2 * Real.pi)) φ) v := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 ((star (regularCharacterUnitary (H := H) l) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularFrequencyPacket φ v)) :
    RegularCoreHilbert H) = 𝓕 (regularFrequencyPacket _ v)
  have hf (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
      (𝓕 (regularFrequencyPacket ψ v) : RegularCoreHilbert H) = regularTensorVector ψ v :=
    (Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply _
  rw [fourier_character_star_apply, hf, hf]
  exact regularTranslateApply_tensorVector _ φ v

theorem regularFrequencyPacket_smul (c : ℂ)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularFrequencyPacket (c • φ) v = c • regularFrequencyPacket φ v := by
  simp only [regularFrequencyPacket, map_smul, smul_apply]

theorem coreTraceFrequencyVector_dual_scaling (a : ℝ) (Ω : H) :
    regularFrequencyWindow 0 1
      ((star (regularCharacterUnitary (H := H) (2 * Real.pi * a)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (coreTraceFrequencyVector Ω)) =
      (Real.exp (Real.pi * a) : ℂ) •
        regularFrequencyWindow (-a) (1 - a) (coreTraceFrequencyVector Ω) := by
  have ha : 2 * Real.pi * a / (2 * Real.pi) = a := by
    field_simp [Real.pi_ne_zero]
  rw [coreTraceFrequencyVector, regularCharacterStar_frequencyPacket, ha,
    regularFrequencyWindow_packet, coreTraceFrequencyScalar_shift,
    regularFrequencyPacket_smul, regularFrequencyWindow_packet]

/-- On the overlap of two windows the dual translate scales the trace vector. -/
theorem coreTraceFrequencyVector_supported_scaling (a : ℝ) (Ω : H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT₀ : T * regularFrequencyWindow 0 1 = T)
    (hTₐ : T * regularFrequencyWindow (-a) (1 - a) = T) :
    T ((star (regularCharacterUnitary (H := H) (2 * Real.pi * a)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (coreTraceFrequencyVector Ω)) =
      (Real.exp (Real.pi * a) : ℂ) • T (coreTraceFrequencyVector Ω) := by
  have h₀ (v : RegularCoreHilbert H) : T (regularFrequencyWindow 0 1 v) = T v := by
    simpa only [mul_apply_eq_comp] using congrArg (fun S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => S v) hT₀
  have hₐ : T (regularFrequencyWindow (-a) (1 - a) (coreTraceFrequencyVector Ω)) =
      T (coreTraceFrequencyVector Ω) := by
    simpa only [mul_apply_eq_comp] using
      congrArg (fun S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => S (coreTraceFrequencyVector Ω)) hTₐ
  rw [← h₀, coreTraceFrequencyVector_dual_scaling, map_smul, hₐ]

end

end KadisonKastler

end OAI
