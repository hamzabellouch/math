import OAI.Analysis.KadisonKastler.RegularPacketCoefficients
import OAI.Analysis.KadisonKastler.DiagonalLocality
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Group.Integral

namespace OAI

/-! # Continuous frames from translated localizations

A finite-measure scalar cutoff has an exact Haar-averaged square norm.
This gives the uniform bound needed when averaging local matrix
compressions in the regular commutant proof.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

private theorem integrable_local_translates {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg : Integrable g volume)
    (s : Set ℝ) (hs : volume s ≠ ⊤) :
    Integrable (fun p : ℝ × ℝ => g (p.1 + p.2))
      ((volume.restrict s).prod volume) := by
  let : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs
  have hp := (measurePreserving_prod_add_right (volume.restrict s)
    (volume : Measure ℝ)).integrable_comp_of_integrable
      (hg.comp_snd (volume.restrict s))
  simpa only [Function.comp_def, add_comm] using hp

/-- Integrating all translates of a local integral counts every point
exactly by the measure of the localization set. -/
theorem integral_local_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : Integrable g volume)
    (s : Set ℝ) (hs : volume s ≠ ⊤) :
    (∫ r : ℝ, ∫ t in s, g (t + r)) = (volume s).toReal • ∫ t : ℝ, g t := by
  have hp := integrable_local_translates hg s hs
  rw [← integral_integral_swap hp]
  simp_rw [integral_add_left_eq_self]
  rw [integral_const, measureReal_def, Measure.restrict_apply_univ]

theorem integrable_integral_local_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Integrable g volume)
    (s : Set ℝ) (hs : volume s ≠ ⊤) :
    Integrable (fun r : ℝ => ∫ t in s, g (t + r)) volume :=
  (integrable_local_translates hg s hs).integral_prod_right

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem norm_local_translation_sq
    (s : Set ℝ) (hs : MeasurableSet s) (f : RegularCoreHilbert H) (r : ℝ) :
    ‖regularIndicatorProjection s hs
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)‖ ^ 2 =
      ∫ t in s, ‖f (t + r)‖ ^ 2 := by
  rw [← regular_setIntegral_norm_sq]
  apply integral_congr_ae
  filter_upwards [(regularRightTranslation_apply_ae
    (Multiplicative.ofAdd r) f).filter_mono (ae_restrict_le)] with t ht
  exact congrArg (fun x : H => ‖x‖ ^ 2) ht

/-- Translated cutoffs form a tight continuous frame. -/
theorem integral_norm_local_translation_sq
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (f : RegularCoreHilbert H) :
    (∫ r : ℝ, ‖regularIndicatorProjection s hs
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)‖ ^ 2) =
      (volume s).toReal * ‖f‖ ^ 2 := by
  simp_rw [norm_local_translation_sq]
  rw [integral_local_translates
    ((Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) s hfinite,
    regular_integral_norm_sq, smul_eq_mul]

/-- The continuous frame's square norms are integrable. -/
theorem integrable_norm_local_translation_sq
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (f : RegularCoreHilbert H) :
    Integrable (fun r : ℝ => ‖regularIndicatorProjection s hs
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)‖ ^ 2) volume := by
  simp_rw [norm_local_translation_sq]
  exact integrable_integral_local_translates
    ((Lp.memLp f).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)) s hfinite

end

end KadisonKastler

end OAI
