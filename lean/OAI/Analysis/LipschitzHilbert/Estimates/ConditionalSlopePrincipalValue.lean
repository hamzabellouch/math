import OAI.Analysis.LipschitzHilbert.Fourier.GlobalBandPrincipalValue
import OAI.Analysis.LipschitzHilbert.Fourier.PublishedBandReductionInput

namespace OAI

/-! The full principal-value bound for small bounded slope fields follows
from the proved global band theorem and the precise published reduction. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem sharpBandOperator_add_profile (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p q : SchwartzMap ℝ ℂ)
    (w : ℝ) (hw : 0<w) :
    sharpBandOperator epsilon R he hR field hfield (p+q) w=
      sharpBandOperator epsilon R he hR field hfield p w+
        sharpBandOperator epsilon R he hR field hfield q w := by
  apply ContinuousLinearMap.ext
  intro f
  change shortL2Operator _ _ _ _ _ (verticalL2Projection (p+q) w f)=
    shortL2Operator _ _ _ _ _ (verticalL2Projection p w f)+
      shortL2Operator _ _ _ _ _ (verticalL2Projection q w f)
  rw [verticalL2Projection_add_profile p q w hw]
  simp only [add_apply,map_add]

theorem global_narrow_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) :
    ∃ B : ℝ, 0<B ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/10000 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
      ‖sharpBandOperator epsilon R he (he.trans_le heR) field hfield narrowBandProfile w‖≤B := by
  obtain ⟨B₁,hB₁,hpos⟩ := global_positive_band_operator_norm hVariation hLL hH narrowBandPositive narrowBandPositive_band
  obtain ⟨B₂,hB₂,hneg⟩ := global_negative_band_operator_norm hVariation hLL hH narrowBandPositive narrowBandPositive_band
  refine ⟨B₁+B₂,add_pos hB₁ hB₂,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb
  rw [narrowBandProfile,sharpBandOperator_add_profile _ _ _ _ _ _ _ _ w hw]
  exact (norm_add_le _ _).trans (add_le_add
    (hpos epsilon R w he heR hR hw field hfield hfb)
    (hneg epsilon R w he heR hR hw field hfield hfb))

theorem conditional_slope_principalValue (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ R : ℝ, 0<R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f) 2 planeMeasure≤
        ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨B,hB,hband⟩ := global_narrow_band_operator_norm hVariation hLL hH
  obtain ⟨C,hC,hfull⟩ := hReassembly B hB
  refine ⟨C,hC,?_⟩
  intro R hR hRsmall field hfield hfb f
  apply hfull R hR hRsmall field hfield hfb _ f
  intro w hw g
  exact band_principalValue_of_uniform_norm field hfield narrowBandProfile w hw R hR
    (by linarith only [hRsmall]) B hB.le
    (fun epsilon he heR => hband epsilon R w he heR hRsmall hw field hfield hfb) g

end LipschitzHilbert.PacketRepresentation

end

end OAI
