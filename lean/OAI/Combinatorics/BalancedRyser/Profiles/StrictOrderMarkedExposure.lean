import Mathlib.Order.RelClasses
import OAI.Combinatorics.BalancedRyser.Profiles.MarkedExposure

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Balanced.MarkedExposure

variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem intersection_le_pow_of_strict_order
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ι → ι → Prop) [IsStrictTotalOrder ι R]
    (E : ι → Set Ω) (s : Finset ι) (p : ℝ≥0∞)
    (hstep : ∀ j ∈ s, ∀ t : Finset ι, t ⊆ s → (∀ i ∈ t, R i j) →
      μ (E j ∩ (⋂ i ∈ t, E i)) ≤ p * μ (⋂ i ∈ t, E i))
    (t : Finset ι) (ht : t ⊆ s) :
    μ (⋂ i ∈ t, E i) ≤ p ^ t.card := by
  classical
  let : LinearOrder ι := linearOrderOfSTO R
  induction t using Finset.induction_on_max with
  | empty => simp
  | insert j t hj ih =>
    have hjs : j ∈ s := ht (Finset.mem_insert_self j t)
    have hts : t ⊆ s := fun i hi => ht (Finset.mem_insert_of_mem hi)
    have hjt : j ∉ t := fun h => (hj j h).false
    have hbefore : ∀ i ∈ t, R i j := hj
    calc
      μ (⋂ i ∈ insert j t, E i) = μ (E j ∩ (⋂ i ∈ t, E i)) := by
        congr 1
        ext ω
        simp
      _ ≤ p * μ (⋂ i ∈ t, E i) := hstep j hjs t hts hbefore
      _ ≤ p * p ^ t.card := mul_le_mul_right (ih hts) p
      _ = p ^ (insert j t).card := by
        rw [Finset.card_insert_of_notMem hjt, pow_succ']

theorem tail_le_choose_mul_of_strict_order
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ι → ι → Prop) [IsStrictTotalOrder ι R]
    (E : ι → Set Ω) (s : Finset ι) (r : ℕ) (p : ℝ≥0∞)
    (hstep : ∀ j ∈ s, ∀ t : Finset ι, t ⊆ s → (∀ i ∈ t, R i j) →
      μ (E j ∩ (⋂ i ∈ t, E i)) ≤ p * μ (⋂ i ∈ t, E i)) :
    μ (atLeast s E r) ≤ (s.card.choose r : ℝ≥0∞) * p ^ r := by
  apply tail_le_choose_mul μ s E r p
  intro t ht
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
  simpa only [hcard] using
    intersection_le_pow_of_strict_order μ R E s p hstep t hsub

theorem tail_le_two_pow_mul_of_strict_order
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ι → ι → Prop) [IsStrictTotalOrder ι R]
    (E : ι → Set Ω) (s : Finset ι) (r : ℕ) (p : ℝ≥0∞)
    (hstep : ∀ j ∈ s, ∀ t : Finset ι, t ⊆ s → (∀ i ∈ t, R i j) →
      μ (E j ∩ (⋂ i ∈ t, E i)) ≤ p * μ (⋂ i ∈ t, E i)) :
    μ (atLeast s E r) ≤ (2 : ℝ≥0∞) ^ s.card * p ^ r := by
  apply tail_le_two_pow_mul μ s E r p
  intro t ht
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
  simpa only [hcard] using
    intersection_le_pow_of_strict_order μ R E s p hstep t hsub

end Balanced.MarkedExposure

end OAI
