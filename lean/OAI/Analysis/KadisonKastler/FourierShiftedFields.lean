import OAI.Analysis.KadisonKastler.ShiftedFrequencyFields
import OAI.Analysis.KadisonKastler.L2Intertwining

namespace OAI

/-! # Fourier coordinates of the shifted frequency field -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

def scalarFourierCut (a : ℝ) : RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).conjStarAlgEquiv (regularFrequencyProjection a)

theorem scalarFourierCut_apply_ae (a : ℝ) (f : RegularCoreHilbert ℂ) :
    scalarFourierCut a f =ᵐ[volume] (Set.Ioi (a / (2 * Real.pi))).indicator f := by
  have h := regularFrequencyProjection_apply_fourier a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
    (regularFrequencyProjection a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)) =ᵐ[volume]
    (Set.Ioi (a / (2 * Real.pi))).indicator
      ((Lp.fourierTransformₗᵢ ℝ ℂ) ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)) at h
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
    (regularFrequencyProjection a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f)) =ᵐ[volume] _
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

theorem scalarFourierCut_norm (a : ℝ) : ‖scalarFourierCut a‖ ≤ 1 := by
  rw [scalarFourierCut, StarAlgEquiv.norm_map]
  exact (regularFrequencyProjection_isStarProjection a).norm_le _

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

include hl in
theorem fourierShiftedField_measurable (a : ℝ) (f : RegularCoreHilbert ℂ) :
    AEStronglyMeasurable (fun s => scalarFourierCut (a - l s) f) μ := by
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp_aestronglyMeasurable
    (shiftedFrequencyField_measurable μ l hl a ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f))

def fourierShiftedField (a : ℝ) :
    Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
  regularFieldOperator μ (fun s => scalarFourierCut (a - l s))
    (fourierShiftedField_measurable μ l hl a) 1
    (Eventually.of_forall fun _ => scalarFourierCut_norm _)

theorem fourierShiftedField_apply_ae (a : ℝ) (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    fourierShiftedField μ l hl a F =ᵐ[μ] fun s => scalarFourierCut (a - l s) (F s) :=
  regularFieldOperator_represents μ _ _ _ _ F

theorem fourierShiftedField_intertwines (a : ℝ) (F : Lp (RegularCoreHilbert ℂ) 2 μ) :
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (shiftedFrequencyField μ l hl a F) =
    fourierShiftedField μ l hl a
      ((Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp F) := by
  apply compLp_regularFieldOperator μ
    (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    (fun s => regularFrequencyProjection (a - l s)) (fun s => scalarFourierCut (a - l s))
    (shiftedFrequencyField_measurable μ l hl a) (fourierShiftedField_measurable μ l hl a) 1 1
    (Eventually.of_forall fun _ => (regularFrequencyProjection_isStarProjection _).norm_le _)
    (Eventually.of_forall fun _ => scalarFourierCut_norm _)
  intro s f
  change (Lp.fourierTransformₗᵢ ℝ ℂ) (regularFrequencyProjection (a - l s) f) =
    (Lp.fourierTransformₗᵢ ℝ ℂ) (regularFrequencyProjection (a - l s)
      ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ((Lp.fourierTransformₗᵢ ℝ ℂ) f)))
  rw [LinearIsometryEquiv.symm_apply_apply]

end

end KadisonKastler

end OAI
