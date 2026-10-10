import OAI.Analysis.LipschitzHilbert.Estimates.ConditionalSlopeOperator
import OAI.Analysis.LipschitzHilbert.Estimates.VariableEndpointOperator

namespace OAI

/-! The full-frequency slope estimate allows measurable, comparably
scaled inner and outer endpoints. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem conditional_variable_slope_truncation (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (hReassembly : BandToFullInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R → R≤1/10000 →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (a : (ℝ×ℝ) → ℝ), Measurable a → (∀ z, 1/2≤a z) → (∀ z, a z≤1) →
    ∀ f : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
        (epsilon*a z) (R*a z) f z) 2 planeMeasure ∧
      eLpNorm (fun z => productSymmetricTruncation (fun z => field (planeCoordinates z))
        (epsilon*a z) (R*a z) f z) 2 planeMeasure≤ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨C,hC,hbound⟩ := conditional_slope_truncation hVariation hLL hH hReassembly
  refine ⟨C+24*Real.pi,by positivity,?_⟩
  intro epsilon R he heR hR field hfield hfb a ham ha ha1 f
  let u := fun z => field (planeCoordinates z)
  have hu : LipschitzWith 2 u := by
    simpa only [mul_one] using product_slope_lipschitz field hfield
  have heq : (fun z => productSymmetricTruncation u (epsilon*a z) (R*a z) f z)=
      endpointErrorOperator epsilon R a u f+shortSlopeOperator (sharpTimeKernel epsilon R) u f := by
    funext z
    have h := endpointErrorOperator_eq_sub epsilon R he heR (by linarith only [hR]) a u ha ha1 f z
    exact (eq_sub_iff_add_eq.mp h).symm
  rw [heq]
  have hmem := (endpointErrorOperator_energy epsilon R he (he.trans_le heR) a u ham ha ha1 hu
    f f.continuous.measurable (f.memLp 2 planeMeasure)).1
  refine ⟨hmem.add (shortSchwartz_memLp _ (sharpTimeKernel_measurable epsilon R)
    (sharpTimeKernel_integrable epsilon R he (he.trans_le heR)) u hu f),?_⟩
  calc
    _ ≤ eLpNorm (endpointErrorOperator epsilon R a u f) 2 planeMeasure+
        eLpNorm (shortSlopeOperator (sharpTimeKernel epsilon R) u f) 2 planeMeasure :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal ((24*Real.pi)*‖f.toLp 2 planeMeasure‖)+
        ENNReal.ofReal (C*‖f.toLp 2 planeMeasure‖) :=
      add_le_add (endpointErrorOperator_bound epsilon R he (he.trans_le heR) a u ham ha ha1 hu f)
        (hbound epsilon R he heR hR field hfield hfb f)
    _ = ENNReal.ofReal ((C+24*Real.pi)*‖f.toLp 2 planeMeasure‖) := by
      rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
