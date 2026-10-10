import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftTailCount
import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftInitialSegment

namespace OAI

/-! # Fixed-shift counting, manuscript Lemma 2.1

The proof uses the proved additive sieve, exact missing-class weights, Mertens
bounds, and integer-root cutoffs. All removed initial points are restored.
-/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem fixed_shift_count (B : Finset ℕ) (hB : B.Nonempty) (C : Set ℕ)
    (N₀ : ℕ) (hprime : ∀ a ∈ C, N₀ ≤ a → ∀ b ∈ B, (a + b).Prime) :
    ∃ E : ℝ, 0 < E ∧ ∀ᶠ N : ℕ in atTop,
      ((summandPrefix C N).card : ℝ) ≤ E * N / Real.log (N : ℝ) ^ B.card := by
  obtain ⟨D, hD, htail⟩ := fixed_shift_tail_count B hB C N₀ hprime
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    (sqrt_log_power_initial_small B.card (N₀ : ℝ) (Nat.cast_nonneg N₀))
  refine ⟨D + 1, by positivity, ?_⟩
  filter_upwards [htail, hsmall, eventually_ge_atTop (2 : ℕ)] with N ht hs hN
  let Q := Nat.nthRoot (20 * B.card) N ^ (10 * B.card)
  change ((summandTail C (Q + N₀) N).card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ D * N at ht
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hQsq : Q ^ 2 ≤ N := fixedShiftRoot_square_cutoff B.card N hB.card_pos
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hQsq
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hL : 0 < Real.log (N : ℝ) ^ B.card := pow_pos hl _
  have hremoved : ((Q : ℝ) + N₀ + 1) * Real.log (N : ℝ) ^ B.card ≤ N := by
    calc
      _ ≤ (Real.sqrt (N : ℝ) + N₀ + 1) * Real.log (N : ℝ) ^ B.card := by
        gcongr
      _ ≤ _ := hs
  have hcard : ((summandPrefix C N).card : ℝ) ≤
      ((Q : ℝ) + N₀ + 1) + (summandTail C (Q + N₀) N).card := by
    exact_mod_cast summandPrefix_card_le_initial_add_tail C (Q + N₀) N
  have hm := mul_le_mul_of_nonneg_right hcard hL.le
  apply (le_div_iff₀ hL).mpr
  nlinarith

end Ostmann

end OAI
