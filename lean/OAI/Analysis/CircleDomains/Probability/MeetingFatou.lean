import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace OAI

/-! Fatou's lemma controls an outer meeting event from eventual occupation
lower bounds. No measurability of the event itself is required. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CircleDomainRigidity

theorem measure_event_le_of_eventual_unit_integrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω)
    (I : ℕ → Ω → ℝ≥0∞) (hI : ∀ n, Measurable (I n)) {B : ℝ≥0∞}
    (hlower : ∀ p ∈ E, ∀ᶠ n in atTop, 1 ≤ I n p)
    (hupper : ∀ᶠ n in atTop, (∫⁻ p, I n p ∂μ) ≤ B) : μ E ≤ B := by
  apply (meas_le_lintegral₀ (Measurable.liminf hI).aemeasurable
    (fun p hp => le_liminf_of_le (by isBoundedDefault) (hlower p hp))).trans
  apply (lintegral_liminf_le hI).trans
  exact le_trans liminf_le_limsup (limsup_le_of_le (by isBoundedDefault) hupper)

end CircleDomainRigidity

end OAI
