import OAI.Combinatorics.BalancedRyser.Local.LocalInjectionBudget
import OAI.Combinatorics.BalancedRyser.Local.LocalTwoReuseUsedEvents
import OAI.Combinatorics.BalancedRyser.Local.LocalUsedEventUnion

namespace OAI

namespace Balanced.Local.UsedEventUnion

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def injectionAverage (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) : ℝ :=
  (∑ e : DirectionToken b κ ↪ Direction F,
    conditionedOffsetProbability (Aligned P (tokenInjectionEquiv F b κ e).1 bits p)
      (E (tokenInjectionEquiv F b κ e).1)) /
    Fintype.card (DirectionToken b κ ↪ Direction F)

def injectionWeight (F : Type*) [Fintype F] (b κ : ℕ)
    (a : DirectionAssignment F b κ) : ℝ :=
  if AllTokensDistinct a then (Fintype.card (DirectionToken b κ ↪ Direction F) : ℝ)⁻¹
    else 0

omit [Field F] [DecidableEq F] in
theorem injectionWeight_nonneg (a : DirectionAssignment F b κ) :
    0 ≤ injectionWeight F b κ a := by
  unfold injectionWeight
  split_ifs <;> positivity

omit [Field F] [DecidableEq F] in
theorem injectionWeight_support (a : DirectionAssignment F b κ)
    (ha : injectionWeight F b κ a ≠ 0) : AllTokensDistinct a := by
  by_contra h
  exact ha (by simp [injectionWeight, h])

theorem injectionAverage_eq_alignedAverage
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (E : DirectionAssignment F b κ → MergedPairs F → Prop) :
    injectionAverage P bits p E = alignedAverage P bits p (injectionWeight F b κ) E := by
  unfold injectionAverage alignedAverage injectionWeight
  rw [← TwoReuseAssembly.sum_allTokensDistinct_eq
    (fun a => conditionedOffsetProbability (Aligned P a bits p) (E a))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : AllTokensDistinct a
  · simp only [ha, ite_true, div_eq_mul_inv, mul_comm]
  · simp only [ha, ite_false, zero_div, zero_mul]

theorem usedEventMean_eq_injectionAverage
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) :
    TwoReuseAssembly.usedEventMean P bits p =
      injectionAverage P bits p
        (fun a M => Admissible P a bits p M ∧ FourEvents.UsedPairExtra P a bits M) +
      injectionAverage P bits p
        (fun a M => Admissible P a bits p M ∧
          FourEvents.ForbiddenCollinearTriple P a bits p M) := by
  simp only [TwoReuseAssembly.usedEventMean, TwoReuseAssembly.usedEventConditionalMass,
    injectionAverage, Finset.sum_add_distrib, add_div]

theorem usedEventMean_le_of_test_bounds
    (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) (hb : 1 ≤ b)
    (hused : ∀ c ij s, injectionAverage P bits p
      (fun a => usedConstituentTest P a bits p c ij s) ≤ 2 / (Fintype.card F : ℝ))
    (htriple : ∀ i j k, injectionAverage P bits p
      (fun a => collinearTest P a bits p i j k) ≤ 2 / (Fintype.card F : ℝ)) :
    TwoReuseAssembly.usedEventMean P bits p ≤
      192 * (b : ℝ) ^ 3 / Fintype.card F := by
  have h₂ := alignedAverage_usedPairExtra_le P bits p (injectionWeight F b 2)
    injectionWeight_nonneg
    (fun a ha => (allTokensDistinct_eligible P a (injectionWeight_support a ha)).2.1)
    (show 0 ≤ 2 / (Fintype.card F : ℝ) by positivity)
    (fun c ij s => by rw [← injectionAverage_eq_alignedAverage]; exact hused c ij s)
  have h₃ := alignedAverage_forbiddenTriple_le P bits p (injectionWeight F b 2)
    injectionWeight_nonneg
    (fun i j k => by rw [← injectionAverage_eq_alignedAverage]; exact htriple i j k)
  rw [← injectionAverage_eq_alignedAverage] at h₂ h₃
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hpow : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (b : ℝ)]
  rw [usedEventMean_eq_injectionAverage]
  calc
    _ ≤ 32 * (b : ℝ) ^ 2 * (2 / (Fintype.card F : ℝ)) +
        64 * (b : ℝ) ^ 3 * (2 / (Fintype.card F : ℝ)) := add_le_add h₂ h₃
    _ ≤ 32 * (b : ℝ) ^ 3 * (2 / (Fintype.card F : ℝ)) +
        64 * (b : ℝ) ^ 3 * (2 / (Fintype.card F : ℝ)) := by
      gcongr
    _ = _ := by ring

universe u

theorem pencilTwoReuses_of_injection_test_bounds
    (hused : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ b : ℕ, 3 ≤ b → 10 * b ≤ Fintype.card F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) c ij s,
        injectionAverage P bits p (fun a => usedConstituentTest P a bits p c ij s) ≤
          2 / (Fintype.card F : ℝ))
    (htriple : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ b : ℕ, 3 ≤ b → 10 * b ≤ Fintype.card F →
      ∀ (P : EqualityPattern b 2) (bits : Bits b) (p : Point F) i j k,
        injectionAverage P bits p (fun a => collinearTest P a bits p i j k) ≤
          2 / (Fintype.card F : ℝ)) : PencilTwoReusesResult.{u} := by
  apply TwoReuseAssembly.pencilTwoReuses_of_used_event_mean
  obtain ⟨q₀, hq₀⟩ := exists_logBudget_token_threshold.{u}
  refine ⟨192, by norm_num, q₀, ?_⟩
  intro F _ _ _ hq b hb hB P bits p
  exact usedEventMean_le_of_test_bounds P bits p (by omega)
    (hused F b hb (hq₀ F hq b hB) P bits p)
    (htriple F b hb (hq₀ F hq b hB) P bits p)

end
end Balanced.Local.UsedEventUnion

end OAI
