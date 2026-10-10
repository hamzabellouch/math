import OAI.Analysis.LipschitzHilbert.Estimates.ConditionalSlopePrincipalValue
import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePVTruncation

namespace OAI

/-! Full-frequency uniform sharp-truncation bounds for bounded small
slope fields, conditional only on the four precisely cited inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def sharpSlopeOperator (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  shortL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
    (by simpa only [mul_one] using product_slope_lipschitz field hfield)

theorem conditional_slope_truncation (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z)) f)
        2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨C,hC,hpv⟩ := conditional_slope_principalValue hVariation hLL hH hReassembly
  refine ⟨2*C,by positivity,?_⟩
  intro epsilon R he heR hR field hfield hfb f
  obtain ⟨_,hlarge⟩ := hpv R (he.trans_le heR) hR field hfield hfb f
  obtain ⟨_,hsmall⟩ := hpv epsilon he (heR.trans hR) field hfield hfb f
  rw [shortSharp_eq_pv_sub _ f f.differentiable epsilon R he heR (by linarith only [hR])]
  have h := (eLpNorm_sub_le (μ:=planeMeasure) (p:=2) (by norm_num)
    (f:=productSlopePrincipalValue (fun z => field (planeCoordinates z)) R f)
    (g:=productSlopePrincipalValue (fun z => field (planeCoordinates z)) epsilon f)).trans
      (add_le_add hlarge hsmall)
  apply h.trans_eq
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem conditional_slope_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/10000 →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
      ‖sharpSlopeOperator epsilon R he (he.trans_le heR) field hfield‖≤C := by
  obtain ⟨C,hC,hbound⟩ := conditional_slope_truncation hVariation hLL hH hReassembly
  refine ⟨C,hC,?_⟩
  intro epsilon R he heR hR field hfield hfb
  let T := sharpSlopeOperator epsilon R he (he.trans_le heR) field hfield
  have hs (g : SchwartzMap (ℝ×ℝ) ℂ) : ‖T (g.toLp 2 planeMeasure)‖≤C*‖g.toLp 2 planeMeasure‖ := by
    have hn := hbound epsilon R he heR hR field hfield hfb g
    have hm := shortSchwartz_memLp (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he (he.trans_le heR)) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) g
    have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal (C*‖g.toLp 2 planeMeasure‖)≠∞) hn
    rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (norm_nonneg _))] at hreal
    change ‖shortL2Operator _ _ _ _ _ (g.toLp 2 planeMeasure)‖≤_
    rw [shortL2Operator_onSchwartz]
    change ‖hm.toLp (shortSlopeOperator (sharpTimeKernel epsilon R) (fun z => field (planeCoordinates z)) g)‖≤_
    rw [Lp.norm_toLp]
    exact hreal
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro f
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  exact hd.induction_on f (isClosed_le (by fun_prop) (by fun_prop)) hs

end LipschitzHilbert.PacketRepresentation

end

end OAI
