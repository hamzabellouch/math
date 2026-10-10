import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace OAI

/-! # Normalized measure on an independent endpoint domain

Normalizing the restricted coordinate measure produces a probability on
the endpoint subtype. A bad set of probability below one half leaves at
least half of the original coordinate volume.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {V : Type*} [MeasurableSpace V]

/-- Probability normalization on the endpoint subtype. -/
def normalizedEndpointMeasure (μ : Measure V) (S : Set V) : Measure S :=
  (μ S)⁻¹ • μ.comap Subtype.val

theorem normalizedEndpointMeasure_isProbability (μ : Measure V) {S : Set V}
    (hS : MeasurableSet S) (h₀ : μ S ≠ 0) (hfin : μ S ≠ ⊤) :
    IsProbabilityMeasure (normalizedEndpointMeasure μ S) := by
  constructor
  rw [normalizedEndpointMeasure, Measure.smul_apply, smul_eq_mul,
    comap_subtype_coe_apply hS, image_univ, Subtype.range_coe]
  exact ENNReal.inv_mul_cancel h₀ hfin

/-- Recover original coordinate volume from the normalized probability. -/
theorem endpoint_volume_eq_mass_mul_probability (μ : Measure V) {S : Set V}
    (hS : MeasurableSet S) (h₀ : μ S ≠ 0) (hfin : μ S ≠ ⊤) (A : Set S) :
    μ (Subtype.val '' A) = μ S * normalizedEndpointMeasure μ S A := by
  rw [normalizedEndpointMeasure, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel h₀ hfin, one_mul, comap_subtype_coe_apply hS]

/-- The good endpoints retain half the original coordinate mass. -/
theorem half_volume_le_good_endpoints (μ : Measure V) {S : Set V}
    (hS : MeasurableSet S) (h₀ : μ S ≠ 0) (hfin : μ S ≠ ⊤)
    {B : Set S} (hB : MeasurableSet B)
    (hbad : normalizedEndpointMeasure μ S B < 1 / 2) :
    μ S * (1 / 2) ≤ μ (Subtype.val '' Bᶜ) := by
  let ν := normalizedEndpointMeasure μ S
  let : IsProbabilityMeasure ν := normalizedEndpointMeasure_isProbability μ hS h₀ hfin
  have hh : (1 / 2 : ℝ≥0∞) ≤ ν Bᶜ := by
    have he := prob_add_prob_compl (μ := ν) hB
    have hb : ν B ≤ 1 / 2 := hbad.le
    have hsum : (1 / 2 : ℝ≥0∞) + 1 / 2 ≤ 1 / 2 + ν Bᶜ := by
      calc
        _ = 1 := ENNReal.add_halves _
        _ = ν B + ν Bᶜ := he.symm
        _ ≤ _ := add_le_add hb le_rfl
    exact (ENNReal.add_le_add_iff_left (by norm_num)).mp hsum
  rw [endpoint_volume_eq_mass_mul_probability μ hS h₀ hfin Bᶜ]
  exact mul_le_mul' le_rfl hh

end PolycyclicRecognition

end

end OAI
