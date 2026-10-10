import OAI.Analysis.KadisonKastler.CharacterContinuity
import OAI.Analysis.KadisonKastler.FrequencyCovariance
import OAI.Analysis.KadisonKastler.RegularCoreIntersection

namespace OAI

/-! # Measurable fields of shifted Fourier cuts -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem star_regularCharacterUnitary (a : ℝ) :
    star (regularCharacterUnitary (H := H) a) = regularCharacterUnitary (H := H) (-a) :=
  regularGroup_star_eq (regularCharacterRepresentation (H := H)) a

theorem character_frequency_cut (a b : ℝ) :
    (star (regularCharacterUnitary (H := H) b) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) *
      regularFrequencyProjection a *
      (regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
    regularFrequencyProjection (a - b) := by
  have hb : 2 * Real.pi * (b / (2 * Real.pi)) = b := by field_simp
  have h := regularFrequencyProjection_character_intertwine (H := H) a (b / (2 * Real.pi))
  rw [hb] at h
  rw [mul_assoc, h, ← mul_assoc,
    Unitary.star_mul_self_of_mem (regularCharacterUnitary (H := H) b).property, one_mul]

theorem continuous_shiftedFrequencyProjection (a : ℝ) (f : RegularCoreHilbert H) :
    Continuous (fun b : ℝ => regularFrequencyProjection (a - b) f) := by
  have hs (g : RegularCoreHilbert H) : Continuous (fun b : ℝ =>
      (star (regularCharacterUnitary (H := H) b) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) := by
    have he : (fun b : ℝ => (star (regularCharacterUnitary (H := H) b) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) =
        (fun b => (regularCharacterUnitary (H := H) (-b) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) := by
      funext b
      exact congrArg (fun u : unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =>
        (u : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) g) (star_regularCharacterUnitary b)
    rw [he]
    exact (continuous_regularCharacterUnitary g).comp continuous_neg
  have hc := continuous_unitary_field_apply
    (fun b : ℝ => star (regularCharacterUnitary (H := H) b)) hs
    (fun b => regularFrequencyProjection a
      ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f))
    ((regularFrequencyProjection a).continuous.comp (continuous_regularCharacterUnitary f))
  have he (b : ℝ) : (star (regularCharacterUnitary (H := H) b) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyProjection a
        ((regularCharacterUnitary (H := H) b : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) =
      regularFrequencyProjection (a - b) f :=
    congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => T f) (character_frequency_cut a b)
  convert hc using 1
  funext b
  exact (he b).symm

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (l : X → ℝ) (hl : Measurable l)

include hl in
theorem shiftedFrequencyField_measurable (a : ℝ) (f : RegularCoreHilbert H) :
    AEStronglyMeasurable (fun s => regularFrequencyProjection (a - l s) f) μ :=
  ((continuous_shiftedFrequencyProjection a f).stronglyMeasurable.comp_measurable hl).aestronglyMeasurable

def shiftedFrequencyField (a : ℝ) : Lp (RegularCoreHilbert H) 2 μ →L[ℂ] Lp (RegularCoreHilbert H) 2 μ :=
  regularFieldOperator μ (fun s => regularFrequencyProjection (a - l s))
    (shiftedFrequencyField_measurable μ l hl a) 1
    (Eventually.of_forall fun _ => (regularFrequencyProjection_isStarProjection _).norm_le _)

theorem shiftedFrequencyField_apply_ae (a : ℝ) (F : Lp (RegularCoreHilbert H) 2 μ) :
    shiftedFrequencyField μ l hl a F =ᵐ[μ] fun s => regularFrequencyProjection (a - l s) (F s) :=
  regularFieldOperator_represents μ _ _ _ _ F

end

end KadisonKastler

end OAI
