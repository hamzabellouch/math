import OAI.Analysis.KadisonKastler.RegularIntervalAverageEstimate
import OAI.Analysis.KadisonKastler.RegularLocalizedPackets
import OAI.Analysis.KadisonKastler.RegularWeakApproximation

namespace OAI

/-! # Normalized interval averages

The boundary strip has fixed width for fixed compact test vectors.
Dividing the localization average by the interval length therefore
recovers every translation-invariant operator weakly.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem norm_regularCut_translate_le (s : Set ℝ) (hs : MeasurableSet s)
    (r : ℝ) (f : RegularCoreHilbert H) :
    ‖regularIndicatorProjection s hs (regularTranslateApply r f)‖ ≤ ‖f‖ := by
  have h := (regularIndicatorProjection (H := H) s hs).le_opNorm (regularTranslateApply r f)
  have hp := IsStarProjection.norm_le _ (regularIndicatorProjection_isStarProjection (H := H) s hs)
  have hn : ‖regularTranslateApply r f‖ = ‖f‖ :=
    Unitary.norm_map (regularRightTranslation (H := H) (Multiplicative.ofAdd r)) f
  exact h.trans (by rw [hn]; simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hp (norm_nonneg f))

private theorem integrable_localized_coefficient
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (f g : RegularCoreHilbert H) :
    Integrable (fun r : ℝ =>
      inner ℂ (regularIndicatorProjection s hs (regularTranslateApply r f))
        (T (regularIndicatorProjection s hs (regularTranslateApply r g)))) volume := by
  have h := L2.integrable_inner (𝕜 := ℂ) (regularLocalFrame s hs hfinite f)
    (T.compLpL 2 volume (regularLocalFrame s hs hfinite g))
  apply h.congr
  filter_upwards [regularLocalFrameValue_apply_ae s hs hfinite f,
    regularLocalFrameValue_apply_ae s hs hfinite g,
    T.coeFn_compLpL (p := 2) (μ := (volume : Measure ℝ))
      (regularLocalFrame s hs hfinite g)] with r hf hg hT
  change inner ℂ (regularLocalFrameValue s hs hfinite f r)
    (T.compLpL 2 volume (regularLocalFrame s hs hfinite g) r) = _
  rw [hf, hT]
  change inner ℂ _ (T (regularLocalFrameValue s hs hfinite g r)) = _
  rw [hg]

/-- The unnormalized error is confined to a fixed-width boundary strip. -/
theorem regularIntervalAverage_error_le
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ r : ℝ, Commute T (regularRightTranslation (H := H) (Multiplicative.ofAdd r) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    {A R : ℝ} (hA : 0 ≤ A) (hR : A ≤ R) (f g : RegularCoreHilbert H)
    (hf : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc f = f)
    (hg : regularIndicatorProjection (Set.Icc (-A) A) measurableSet_Icc g = g) :
    ‖inner ℂ f (regularLocalizationAverage (Set.Icc (-R) R) measurableSet_Icc
      (by simp [Real.volume_Icc]) T g) - (2 * R : ℝ) • inner ℂ f (T g)‖ ≤
      8 * A * (‖T‖ * (‖f‖ * ‖g‖)) := by
  rw [inner_regularLocalizationAverage]
  apply regular_interval_boundary_estimate hA hR (by positivity)
  · exact integrable_localized_coefficient _ measurableSet_Icc (by simp [Real.volume_Icc]) T f g
  · calc
      ‖inner ℂ f (T g)‖ ≤ ‖f‖ * ‖T g‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖T‖ * ‖g‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  · intro r
    calc
      _ ≤ ‖regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc (regularTranslateApply r f)‖ *
          ‖T (regularIndicatorProjection (Set.Icc (-R) R) measurableSet_Icc (regularTranslateApply r g))‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖T‖ * ‖g‖) :=
        mul_le_mul (norm_regularCut_translate_le _ measurableSet_Icc r f)
          ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (norm_regularCut_translate_le _ measurableSet_Icc r g) (norm_nonneg T)))
          (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  · intro r hr
    rw [regularInterval_translate_eq hr f hf, regularInterval_translate_eq hr g hg]
    have hc := congrArg (fun B : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => B g) (hT r).eq
    change T (regularTranslateApply r g) = regularTranslateApply r (T g) at hc
    rw [hc]
    exact Unitary.inner_map_map (regularRightTranslation (H := H) (Multiplicative.ofAdd r)) f (T g)
  · intro r hr
    rw [regularInterval_translate_zero hr f hf, inner_zero_left]

/-- The interval-length-normalized localization is a contraction on operators. -/
def regularNormalizedIntervalAverage (n : ℕ)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (((2 * ((n : ℝ) + 1))⁻¹ : ℝ) : ℂ) • regularLocalizationAverage
    (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) measurableSet_Icc
    (by simp [Real.volume_Icc]) T

theorem norm_regularNormalizedIntervalAverage_le (n : ℕ)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
    ‖regularNormalizedIntervalAverage n T‖ ≤ ‖T‖ := by
  have hp : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have hm : (volume (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))).toReal =
      2 * ((n : ℝ) + 1) := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Nat.cast_nonneg (α := ℝ) n])]
    ring
  rw [regularNormalizedIntervalAverage, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (2 * ((n : ℝ) + 1))⁻¹ *
        ((volume (Set.Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1))).toReal * ‖T‖) :=
      mul_le_mul_of_nonneg_left (norm_regularLocalizationAverage_le _ measurableSet_Icc
        (by simp [Real.volume_Icc]) T) (inv_nonneg.mpr hp.le)
    _ = _ := by rw [hm, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

end

end KadisonKastler

end OAI
