import OAI.Analysis.LipschitzHilbert.Fourier.GlobalBandOperator
import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValueBound

namespace OAI

/-! The proved global band bounds pass to the actual symmetric principal
value, by the explicit pointwise limit and Fatou. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpBandOperator_eLpNorm_le (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ)
    (w : ℝ) (hw : 0<w) (C : ℝ) (hC : 0≤C)
    (hbound : ‖sharpBandOperator epsilon R he hR field hfield p w‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z))
      (schwartzVerticalProjection p w 0 f)) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  let g := schwartzVerticalProjection p w 0 f
  let u := fun z => field (planeCoordinates z)
  have hu : LipschitzWith 2 u := by simpa only [mul_one] using product_slope_lipschitz field hfield
  have hm := shortSchwartz_memLp (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) u hu g
  have hn := ((sharpBandOperator epsilon R he hR field hfield p w).le_opNorm (f.toLp 2 planeMeasure)).trans
    (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  change ‖bandL2Operator _ _ _ _ _ p w (f.toLp 2 planeMeasure)‖≤_ at hn
  rw [bandL2Operator_onSchwartz _ _ _ _ _ p w hw f] at hn
  change ‖hm.toLp (shortSlopeOperator (sharpTimeKernel epsilon R) u g)‖≤C*‖f.toLp 2 planeMeasure‖ at hn
  rw [Lp.norm_toLp] at hn
  apply (ENNReal.toReal_le_toReal hm.eLpNorm_ne_top (by simp)).mp
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg _))] using hn

theorem band_principalValue_of_uniform_norm (field : Plane → ℝ) (hfield : LipschitzWith 1 field)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w) (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (C : ℝ) (hC : 0≤C)
    (hbound : ∀ epsilon : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield p w‖≤C)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
      (schwartzVerticalProjection p w 0 f)) 2 planeMeasure ∧
    eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
      (schwartzVerticalProjection p w 0 f)) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  have hum : Measurable (fun z => field (planeCoordinates z)) := hfield.continuous.measurable.comp planeCoordinates.measurable
  have hn := productSlopePrincipalValue_eLpNorm_le (fun z => field (planeCoordinates z)) hum
    (schwartzVerticalProjection p w 0 f) (schwartzVerticalProjection p w 0 f).differentiable R hR hRsmall
    (ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖)) (fun epsilon he heR =>
      sharpBandOperator_eLpNorm_le epsilon R he (he.trans_le heR.le) field hfield p w hw C hC
        (hbound epsilon he heR.le) f)
  exact ⟨hn.trans_lt ENNReal.ofReal_lt_top,hn⟩

theorem global_positive_band_principalValue (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ R w : ℝ, 0<R → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (_hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
        (schwartzVerticalProjection p w 0 f)) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
        (schwartzVerticalProjection p w 0 f)) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨C,hC,hbound⟩ := global_positive_band_operator_norm hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro R w hR hRsmall hw field hfield hfb f
  exact band_principalValue_of_uniform_norm field hfield p w hw R hR (by linarith only [hRsmall])
    C hC.le (fun epsilon he heR => hbound epsilon R w he heR hRsmall hw field hfield hfb) f

theorem global_negative_band_principalValue (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ R w : ℝ, 0<R → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (_hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
        (schwartzVerticalProjection (conjugateReflectedCutoff p) w 0 f)) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R
        (schwartzVerticalProjection (conjugateReflectedCutoff p) w 0 f)) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨C,hC,hbound⟩ := global_negative_band_operator_norm hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro R w hR hRsmall hw field hfield hfb f
  exact band_principalValue_of_uniform_norm field hfield (conjugateReflectedCutoff p) w hw R hR
    (by linarith only [hRsmall]) C hC.le
    (fun epsilon he heR => hbound epsilon R w he heR hRsmall hw field hfield hfb) f

end LipschitzHilbert.PacketRepresentation

end

end OAI
