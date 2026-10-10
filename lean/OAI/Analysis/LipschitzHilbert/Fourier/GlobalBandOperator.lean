import OAI.Analysis.LipschitzHilbert.Fourier.GlobalBandLocalization
import OAI.Analysis.LipschitzHilbert.Fourier.NegativeBandOperator

namespace OAI

/-! Global positive and negative vertical-band bounds at one absolute
short scale, conditional on martingale variation, the directional
maximal estimate, and the horizontal Hilbert estimate. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def sharpBandOperator (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w

theorem sharpBandOperator_norm_of_strip_bounds (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (hRsmall : R≤1/10000) (field : Plane → ℝ) (hfield : LipschitzWith 1 field)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) (C : ℝ) (hC : 0≤C)
    (hlocal : ∀ l r : ℝ, 1200*(r-l)≤1 →
      ‖localizedSharpBandOperator epsilon R he hR field hfield p w l r‖≤C) :
    ‖sharpBandOperator epsilon R he hR field hfield p w‖≤3*C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  exact bandL2Operator_global_from_local epsilon R he hR field hfield p w hw (1/10000)
    (by norm_num) hRsmall C hC (fun j => hlocal _ _ (by ring_nf; norm_num)) f

theorem global_positive_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield p w‖≤C := by
  obtain ⟨C,hC,hlocal⟩ := localized_sharp_band_operator_norm hVariation hLL hH p hp
  refine ⟨3*C,by positivity,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb
  apply sharpBandOperator_norm_of_strip_bounds epsilon R he (he.trans_le heR) hR field hfield p w hw C hC.le
  exact hlocal epsilon R w he heR (by linarith only [hR]) hw field hfield hfb

theorem global_negative_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield (conjugateReflectedCutoff p) w‖≤C := by
  obtain ⟨C,hC,hlocal⟩ := localized_negative_band_operator_norm hVariation hLL hH p hp
  refine ⟨3*C,by positivity,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb
  apply sharpBandOperator_norm_of_strip_bounds epsilon R he (he.trans_le heR) hR field hfield
    (conjugateReflectedCutoff p) w hw C hC.le
  exact hlocal epsilon R w he heR (by linarith only [hR]) hw field hfield hfb

end LipschitzHilbert.PacketRepresentation

end

end OAI
