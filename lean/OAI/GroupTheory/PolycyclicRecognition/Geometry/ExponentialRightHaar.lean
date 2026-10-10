import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Right invariance of exponential-coordinate Haar measure

Negation preserves coordinate Lebesgue measure and corresponds to group
inversion. Thus the exponential-coordinate left Haar measure is also right
invariant, without a separate group nilpotence assertion.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

/-- Oddness of an exponential chart makes its coordinate measure invariant
under group inversion. -/
theorem isInvInvariant_map_of_neg
    {V G : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableNeg V]
    [Group G] [MeasurableSpace G] [MeasurableInv G]
    (ν : Measure V) [ν.IsNegInvariant]
    (f : V → G) (hf : Measurable f) (hneg : ∀ x, f (-x) = (f x)⁻¹) :
    (Measure.map f ν).IsInvInvariant := by
  constructor
  change Measure.map Inv.inv (Measure.map f ν) = Measure.map f ν
  rw [Measure.map_map measurable_inv hf]
  have hcomp : Inv.inv ∘ f = f ∘ Neg.neg := by
    funext x
    exact (hneg x).symm
  rw [hcomp, ← Measure.map_map hf measurable_neg, Measure.map_neg_eq_self]

/-- The same coordinate measure is right Haar as soon as it is left invariant. -/
theorem isMulRightInvariant_map_of_neg
    {V G : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableNeg V]
    [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (ν : Measure V) [ν.IsNegInvariant]
    (f : V → G) (hf : Measurable f) (hneg : ∀ x, f (-x) = (f x)⁻¹)
    [(Measure.map f ν).IsMulLeftInvariant] :
    (Measure.map f ν).IsMulRightInvariant := by
  let μ := Measure.map f ν
  let : μ.IsInvInvariant := isInvInvariant_map_of_neg ν f hf hneg
  have hi : μ.inv = μ := Measure.inv_eq_self μ
  change μ.IsMulRightInvariant
  rw [← hi]
  infer_instance

/-- Pull right translation back through the actual coordinate equivalence. -/
theorem coordinate_right_translation_preserving
    {V G : Type*} [MeasurableSpace V] [Group G] [MeasurableSpace G]
    [MeasurableMul G] (ν : Measure V) (μ : Measure G) [μ.IsMulRightInvariant]
    (e : V ≃ᵐ G) (he : Measure.map e ν = μ)
    (m : V → V → V) (hm : ∀ x y, e (m x y) = e x * e y) (q : V) :
    MeasurePreserving (fun x => m x q) ν ν := by
  have hp : MeasurePreserving e ν μ := ⟨e.measurable, he⟩
  have h := (hp.symm e).comp ((measurePreserving_mul_right μ (e q)).comp hp)
  convert h using 1
  funext x
  exact (e.symm_apply_eq.mpr (hm x q).symm).symm

end PolycyclicRecognition

end

end OAI
