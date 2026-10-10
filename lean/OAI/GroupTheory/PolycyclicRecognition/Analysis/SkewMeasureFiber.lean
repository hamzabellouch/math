import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! # Recovering a fiber measure from a measure-preserving skew map -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {Q I : Type*} [Group Q] [Group I]
  [MeasurableSpace Q] [MeasurableSpace I]
  [MeasurableMul₂ Q] [MeasurableInv Q] [MeasurableMul₂ I] [MeasurableInv I]

omit [MeasurableInv Q] in
/-- Cancel the base translation and the right fiber translation, then
test on a rectangle of finite positive base measure. -/
theorem measurePreserving_fiber_of_right_skew
    (ν : Measure Q) (μ : Measure I) [SFinite ν] [SFinite μ]
    [ν.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (g : Q) (C : I → I) (hC : Measurable C) (a : Q → I) (ha : Measurable a)
    (hskew : MeasurePreserving (fun p : Q × I => (g * p.1, C p.2 * a p.1))
      (ν.prod μ) (ν.prod μ))
    {B : Set Q} (hB : MeasurableSet B) (hB0 : ν B ≠ 0) (hBtop : ν B ≠ ∞) :
    MeasurePreserving C μ μ := by
  let U : Q × I → Q × I := fun p =>
    (g⁻¹ * p.1, p.2 * (a (g⁻¹ * p.1))⁻¹)
  have hU : MeasurePreserving U (ν.prod μ) (ν.prod μ) := by
    apply (measurePreserving_mul_left ν g⁻¹).skew_product
      (g := fun q i => i * (a (g⁻¹ * q))⁻¹)
    · exact measurable_snd.mul ((ha.comp (measurable_const.mul measurable_fst)).inv)
    · exact Filter.Eventually.of_forall fun q => map_mul_right_eq_self μ _
  have hp : MeasurePreserving (fun p : Q × I => (p.1, C p.2))
      (ν.prod μ) (ν.prod μ) := by
    have hh := hU.comp hskew
    simpa only [U, Function.comp_def, inv_mul_cancel_left, mul_inv_cancel_right] using hh
  refine ⟨hC, ?_⟩
  ext S hS
  rw [Measure.map_apply hC hS]
  have hh := hp.measure_preimage (hB.prod hS).nullMeasurableSet
  change (ν.prod μ) (B ×ˢ (C ⁻¹' S)) = (ν.prod μ) (B ×ˢ S) at hh
  simp only [Measure.prod_prod] at hh
  exact (ENNReal.mul_right_inj hB0 hBtop).mp hh

end PolycyclicRecognition

end

end OAI
