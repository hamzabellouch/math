import OAI.NumberTheory.TwoPoint.Bounds.ResidueCentering

namespace OAI

/-! The full divisibility word bound, including exact unlit extra powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- Keep the extra power of every designated nonsingleton. The ambient
prime pool may contain coordinates unused by the word. -/
theorem uniform_divisor_word_reciprocal_bound {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (offset : τ → ℤ) (base : ι → Fin B)
    (R H : ℝ) (hR : 0 ≤ R) (hH : 0 < H) (hpH : ∀ i, H ≤ p i)
    (G : (ι → Fin B) → ℝ) (hG : ∀ z, |G z| ≤ 1) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R * (∏ t,
        ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
          (p (label t) : ℝ)⁻¹)) * G z)| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        R * (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * H⁻¹ ^
          (∑ i ∈ nonsingletonLabels label,
            extraReciprocalExponent (litOccurrences label (designationLit U) i).card
              (unlitOccurrences label (designationLit U) i).card) *
          2 ^ (singletonLabels label).card := by
  rw [uniform_divisor_word_average B p hp hpB label offset R G]
  apply (uniform_centered_word_crude_bound B p hp hpB label
    (fun t => forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)) base
    (fun t => forcedResidue_lt B (p (label t)) (hp _) (hpB _) (offset t)) R hR G hG).trans
  apply sum_le_sum
  intro U hU
  have hc := full_word_designated_reciprocal_bound label U (mem_powerset.mp hU) p H hH hpH
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hR)
      (show 0 ≤ (2 : ℝ) ^ (singletonLabels label).card by positivity)

/-- The exact literal number of unlit slots is bounded by twice the
retained extra exponent, with no hypothesis about unused coordinates. -/
lemma designation_card_le_twice_extra {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] (label : τ → ι) (U : Finset τ) (hU : U ⊆ nonsingletonSlots label) :
    U.card ≤ 2 * ∑ i ∈ nonsingletonLabels label,
      extraReciprocalExponent (litOccurrences label (designationLit U) i).card
        (unlitOccurrences label (designationLit U) i).card := by
  have h := actual_unlit_le_twice_extra label (designationLit U)
  rw [← nonsingleton_unlit_card, designationLit_unlit label U hU] at h
  rw [← sum_coe_sort]
  exact h

end TwoPointCorrelations

end OAI
