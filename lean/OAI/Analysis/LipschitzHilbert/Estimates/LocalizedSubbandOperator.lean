import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedBandOperator
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalHorizontalCutoff
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalProjectionAlgebra

namespace OAI

/-! A bound for an enlarged band controls every subband, with the norm
of the projected input. Horizontal localization commutes with projections. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def localizedSharpOperator (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (l r : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (stripL2Cutoff l r).comp
    ((shortL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield)).comp (stripL2Cutoff l r))

theorem verticalL2Projection_strip (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (l r : ℝ) (f : Lp ℂ 2 planeMeasure) :
    verticalL2Projection p w (stripL2Cutoff l r f)=stripL2Cutoff l r (verticalL2Projection p w f) :=
  verticalL2Projection_horizontal_indicator p w hw (Set.Icc l r) measurableSet_Icc f

theorem localizedSharpBandOperator_subband (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ s, p s*q s=q s) (w : ℝ) (hw : 0<w) (l r : ℝ) (f : Lp ℂ 2 planeMeasure) :
    localizedSharpBandOperator epsilon R he hR field hfield p w l r (verticalL2Projection q w f)=
      localizedSharpOperator epsilon R he hR field hfield l r (verticalL2Projection q w f) := by
  change stripL2Cutoff l r (shortL2Operator _ _ _ _ _
    (verticalL2Projection p w (stripL2Cutoff l r (verticalL2Projection q w f))))=
      stripL2Cutoff l r (shortL2Operator _ _ _ _ _ (stripL2Cutoff l r (verticalL2Projection q w f)))
  rw [←verticalL2Projection_strip q w hw l r f]
  have habs := congrArg (fun T : Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure => T (stripL2Cutoff l r f))
    (verticalL2Projection_absorb p q hpq w hw)
  exact congrArg (fun g => stripL2Cutoff l r (shortL2Operator _ _ _ _ _ g)) habs

theorem localizedSharpOperator_subband_bound (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p q : SchwartzMap ℝ ℂ)
    (hpq : ∀ s, p s*q s=q s) (w : ℝ) (hw : 0<w) (l r C : ℝ)
    (hC : ‖localizedSharpBandOperator epsilon R he hR field hfield p w l r‖≤C)
    (f : Lp ℂ 2 planeMeasure) :
    ‖localizedSharpOperator epsilon R he hR field hfield l r (verticalL2Projection q w f)‖≤
      C*‖verticalL2Projection q w f‖ := by
  rw [←localizedSharpBandOperator_subband epsilon R he hR field hfield p q hpq w hw l r f]
  exact ((localizedSharpBandOperator epsilon R he hR field hfield p w l r).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

end LipschitzHilbert.PacketRepresentation

end

end OAI
