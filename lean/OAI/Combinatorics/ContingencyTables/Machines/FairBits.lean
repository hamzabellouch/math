import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Bounded fair-bit scaling

Both papers for result 200 implement a bounded approximately uniform integer
choice by drawing `z` uniformly from `0,...,Q-1` and returning `⌊M*z/Q⌋`.
When `Q = 2^k`, the input choice uses exactly `k` fair bits.

We prove the exact integer fiber formula in 200-01, equation
`eq:dense-offset-count`, and the pointwise and total-variation error estimates
used in 200-02, Lemma `lem:dyadic-integer-draw`. The arguments are direct
finite arithmetic and have no published-input hypotheses.
-/

open scoped BigOperators

namespace ContingencyTables.FairBits

/-- The bounded scaling map on integer proposals. -/
def scale (M Q z : ℕ) : ℕ := ⌊(M : ℚ) * z / Q⌋₊

/-- The rational floor is exactly the implemented natural integer quotient. -/
lemma scale_eq_div (M Q z : ℕ) : scale M Q z = M * z / Q := by
  rw [scale, ← Nat.cast_mul, Nat.floor_div_eq_div]

/-- The first integer whose scaled value can be at least `β`. -/
def endpoint (M Q β : ℕ) : ℕ := ⌈(β : ℚ) * Q / M⌉₊

/-- The proposal integers that produce a given output. -/
def fiber (M Q β : ℕ) : Finset ℕ :=
  (Finset.range Q).filter fun z => scale M Q z = β

lemma scale_lt {M Q z : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hz : z < Q) :
    scale M Q z < M := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hzq : (z : ℚ) < Q := by exact_mod_cast hz
  rw [scale, Nat.floor_lt (by positivity), div_lt_iff₀ hQq]
  nlinarith

lemma scale_eq_iff {M Q β z : ℕ} (hM : 0 < M) (hQ : 0 < Q) :
    scale M Q z = β ↔ endpoint M Q β ≤ z ∧ z < endpoint M Q (β + 1) := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  rw [scale, Nat.floor_eq_iff (by positivity)]
  simp only [endpoint, Nat.ceil_le, Nat.lt_ceil, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (div_le_iff₀ hMq).mpr
      have h := (le_div_iff₀ hQq).mp hlo
      nlinarith
    · apply (lt_div_iff₀ hMq).mpr
      have h := (div_lt_iff₀ hQq).mp hhi
      nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (le_div_iff₀ hQq).mpr
      have h := (div_le_iff₀ hMq).mp hlo
      nlinarith
    · apply (div_lt_iff₀ hQq).mpr
      have h := (lt_div_iff₀ hMq).mp hhi
      nlinarith

lemma endpoint_le_proposal {M Q β : ℕ} (hM : 0 < M) (hβ : β < M) :
    endpoint M Q (β + 1) ≤ Q := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hβq : ((β + 1 : ℕ) : ℚ) ≤ M := by
    exact_mod_cast Nat.succ_le_of_lt hβ
  rw [endpoint, Nat.ceil_le, div_le_iff₀ hMq]
  nlinarith [mul_le_mul_of_nonneg_right hβq (Nat.cast_nonneg Q : (0 : ℚ) ≤ Q)]

/-- The exact preimage interval, including both endpoint conventions. -/
theorem fiber_eq_interval {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q)
    (hβ : β < M) :
    fiber M Q β = Finset.Ico (endpoint M Q β) (endpoint M Q (β + 1)) := by
  ext z
  simp only [fiber, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  rw [scale_eq_iff hM hQ]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨lt_of_lt_of_le h.2 (endpoint_le_proposal hM hβ), h⟩

/-- This is the ceiling-difference formula used to tabulate the implemented
output law without enumerating all random bit strings. -/
theorem fiber_card {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hβ : β < M) :
    (fiber M Q β).card = endpoint M Q (β + 1) - endpoint M Q β := by
  rw [fiber_eq_interval hM hQ hβ, Nat.card_Ico]

lemma endpoint_mono (M Q β : ℕ) :
    endpoint M Q β ≤ endpoint M Q (β + 1) := by
  apply Nat.ceil_mono
  simp only [Nat.cast_add, Nat.cast_one]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  nlinarith [(Nat.cast_nonneg Q : (0 : ℚ) ≤ Q)]

/-- A scaled output has a number of preimages differing by less than one
from the ideal real-valued number `Q/M`. -/
theorem fiber_card_error {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hβ : β < M) :
    |((fiber M Q β).card : ℚ) - (Q : ℚ) / M| < 1 := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hlo := Nat.le_ceil ((β : ℚ) * Q / M)
  have hhi := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (β : ℚ) * Q / M by positivity)
  have hlo' := Nat.le_ceil (((β + 1 : ℕ) : ℚ) * Q / M)
  have hhi' := Nat.ceil_lt_add_one
    (show (0 : ℚ) ≤ ((β + 1 : ℕ) : ℚ) * Q / M by positivity)
  rw [fiber_card hM hQ hβ, Nat.cast_sub (endpoint_mono M Q β)]
  simp only [endpoint, Nat.cast_add, Nat.cast_one] at *
  rw [abs_lt]
  have hdiff : ((β : ℚ) + 1) * Q / M = (β : ℚ) * Q / M + (Q : ℚ) / M := by ring
  constructor <;> linarith

/-- The exact mass assigned by the finite uniform proposal. -/
def outputMass (M Q β : ℕ) : ℚ := (fiber M Q β).card / (Q : ℚ)

lemma outputMass_nonnegative (M Q β : ℕ) : 0 ≤ outputMass M Q β := by
  dsimp [outputMass]
  positivity

/-- The masses are normalized on the declared output range. -/
theorem outputMass_total {M Q : ℕ} (hM : 0 < M) (hQ : 0 < Q) :
    ∑ β ∈ Finset.range M, outputMass M Q β = 1 := by
  have hc : ∑ β ∈ Finset.range M, (fiber M Q β).card = Q := by
    symm
    simpa only [fiber, Finset.card_range] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.range Q)
        (t := Finset.range M) (f := scale M Q) (by
          intro z hz
          exact Finset.mem_range.mpr (scale_lt hM hQ (Finset.mem_range.mp hz))))
  have hcq : ∑ β ∈ Finset.range M, ((fiber M Q β).card : ℚ) = Q := by
    exact_mod_cast hc
  simp only [outputMass, ← Finset.sum_div, hcq]
  exact div_self (by exact_mod_cast ne_of_gt hQ)

/-- Every point mass differs from uniform by at most `1/Q`. -/
theorem outputMass_error {M Q β : ℕ} (hM : 0 < M) (hQ : 0 < Q) (hβ : β < M) :
    |outputMass M Q β - 1 / (M : ℚ)| ≤ 1 / (Q : ℚ) := by
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hQn : (Q : ℚ) ≠ 0 := ne_of_gt hQq
  have herr := (fiber_card_error hM hQ hβ).le
  have heq : outputMass M Q β - 1 / (M : ℚ) =
      (((fiber M Q β).card : ℚ) - (Q : ℚ) / M) / Q := by
    dsimp [outputMass]
    field_simp
  rw [heq, abs_div, abs_of_pos hQq]
  exact (div_le_div_iff_of_pos_right hQq).mpr herr

/-- Total variation with the manuscript's convention `½ ∑ |p-u|`. -/
def variationFromUniform (M Q : ℕ) : ℚ :=
  (1 / 2) * ∑ β ∈ Finset.range M, |outputMass M Q β - 1 / (M : ℚ)|

/-- The bounded integer draw has total-variation error at most `M/(2Q)`.
The papers use the weaker bound `M/Q`. -/
theorem variation_bound {M Q : ℕ} (hM : 0 < M) (hQ : 0 < Q) :
    variationFromUniform M Q ≤ (M : ℚ) / (2 * Q) := by
  have hsum : (∑ β ∈ Finset.range M, |outputMass M Q β - 1 / (M : ℚ)|) ≤
      (M : ℚ) * (1 / (Q : ℚ)) := by
    calc
      _ ≤ ∑ _β ∈ Finset.range M, (1 / (Q : ℚ)) := by
        apply Finset.sum_le_sum
        intro β hβ
        exact outputMass_error hM hQ (Finset.mem_range.mp hβ)
      _ = _ := by simp
  dsimp [variationFromUniform]
  calc
    _ ≤ (1 / 2 : ℚ) * ((M : ℚ) * (1 / (Q : ℚ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end ContingencyTables.FairBits

end OAI
