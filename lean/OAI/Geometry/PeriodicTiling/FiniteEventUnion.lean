import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat

namespace OAI

universe uΩ uI

namespace PeriodicTilingThree

open scoped BigOperators

theorem exists_avoiding_of_sum_card_lt {Ω : Type uΩ} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω)
    (hsmall : (∑ i ∈ events, (bad i).card) < Fintype.card Ω) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  classical
  have hUnion : (events.biUnion bad).card < (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt Finset.card_biUnion_le hsmall
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hUnion
  refine ⟨ω, ?_⟩
  intro i hi hbad
  exact hω (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩)

theorem exists_avoiding_of_uniform_ratio_lt {Ω : Type uΩ} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω) (r : ℚ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ i ∈ events, ((bad i).card : ℚ) / (Fintype.card Ω : ℚ) ≤ r)
    (hsmall : (events.card : ℚ) * r < 1) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  have hpos : (0 : ℚ) < (Fintype.card Ω : ℚ) := Nat.cast_pos.mpr hΩ
  have hsum : (∑ i ∈ events, ((bad i).card : ℚ)) < (Fintype.card Ω : ℚ) := by
    calc
      (∑ i ∈ events, ((bad i).card : ℚ))
          ≤ ∑ i ∈ events, r * (Fintype.card Ω : ℚ) :=
        Finset.sum_le_sum fun i hi => (div_le_iff₀ hpos).mp (hbound i hi)
      _ = (events.card : ℚ) * r * (Fintype.card Ω : ℚ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ < 1 * (Fintype.card Ω : ℚ) := mul_lt_mul_of_pos_right hsmall hpos
      _ = (Fintype.card Ω : ℚ) := one_mul _
  apply exists_avoiding_of_sum_card_lt events bad
  apply (Nat.cast_lt (α := ℚ)).mp
  simpa only [Nat.cast_sum] using hsum

end PeriodicTilingThree

end OAI
