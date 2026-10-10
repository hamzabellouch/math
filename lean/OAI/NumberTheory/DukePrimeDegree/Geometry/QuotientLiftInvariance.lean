import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLiftMeasure

namespace OAI

/-! # Invariance of the covering lift

Changing the section after a quotient translation is harmless because the
lift is section-independent. Thus every actual right invariance of the
quotient measure lifts to the corresponding right invariance on the group.
-/

noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem quotientLiftMeasure_right_invariant (n : ℕ)
    (μ : Measure (X n)) (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (a : G n) (ha : μ.map (fun x => rightAction x a)=μ) :
    (quotientLiftMeasure n μ s).map (fun g => g*a)=quotientLiftMeasure n μ s := by
  let T : X n → X n := fun x => rightAction x a
  have hT : MeasurePreserving T μ μ := ⟨(continuous_rightAction a).measurable,ha⟩
  let t : X n → G n := fun x => s (T x)*a⁻¹
  have htm : Measurable t := (hsm.comp hT.measurable).mul_const _
  have ht : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (t x)=x := by
    intro x
    change rightAction (Quotient.mk _ (s (T x))) a⁻¹=x
    rw [hs]
    change rightAction (rightAction x a) a⁻¹=x
    rw [rightAction_mul,mul_inv_cancel,rightAction_one]
  conv_lhs => rw [quotientLiftMeasure_section_independent n μ s t hsm htm hs ht]
  ext E hE
  have hR : Measurable (fun g : G n => g*a) := continuous_mul_const a |>.measurable
  rw [Measure.map_apply hR hE,quotientLiftMeasure,Measure.sum_apply _ (hE.preimage hR),
    quotientLiftMeasure,Measure.sum_apply _ hE]
  apply tsum_congr
  intro γ
  have hγt : Measurable (fun x => γ.val*t x) := measurable_const.mul htm
  have hγs : Measurable (fun x => γ.val*s x) := measurable_const.mul hsm
  rw [Measure.map_apply hγt (hE.preimage hR),Measure.map_apply hγs hE]
  have he : (fun x => γ.val*t x) ⁻¹' ((fun g : G n => g*a) ⁻¹' E) =
      T ⁻¹' ((fun x => γ.val*s x) ⁻¹' E) := by
    ext x
    change (γ.val*(s (T x)*a⁻¹))*a ∈ E ↔ γ.val*s (T x) ∈ E
    simp only [mul_assoc,inv_mul_cancel,mul_one]
  rw [he]
  exact hT.measure_preimage (hE.preimage hγs).nullMeasurableSet

end DukePrimeDegree

end

end OAI
