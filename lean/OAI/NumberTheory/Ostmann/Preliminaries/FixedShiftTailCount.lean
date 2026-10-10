import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftPowerCount
import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftRootCutoff
import OAI.NumberTheory.Ostmann.Supply.NaturalPrimeSupportSieve

namespace OAI

/-! # The fixed-shift sieve bound at every sufficiently large endpoint -/

namespace Ostmann

open Filter
open scoped Classical BigOperators

 theorem fixed_shift_tail_count (B : Finset ℕ) (hB : B.Nonempty) (C : Set ℕ)
    (N₀ : ℕ) (hprime : ∀ a ∈ C, N₀ ≤ a → ∀ b ∈ B, (a + b).Prime) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ N : ℕ in atTop,
      let Q := Nat.nthRoot (20 * B.card) N ^ (10 * B.card)
      ((summandTail C (Q + N₀) N).card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ D * N := by
  obtain ⟨D, hD, hcount⟩ := fixed_shift_power_count B hB
  let k := 20 * B.card
  have hk : k ≠ 0 := by dsimp [k]; have := hB.card_pos; omega
  let F : ℝ := (2 * (k : ℝ)) ^ B.card
  have hF : 0 < F := by dsimp [F]; exact pow_pos (by exact_mod_cast (by omega : 0 < 2 * k)) _
  refine ⟨3 * F * D, by positivity, ?_⟩
  have hRcount := (nthRoot_tendsto k hk).eventually hcount
  have hRlarge := (nthRoot_tendsto k hk).eventually (eventually_ge_atTop 2)
  filter_upwards [hRcount, hRlarge, eventually_ge_atTop (2 : ℕ)] with N hN hR hN2
  dsimp only
  let R := Nat.nthRoot k N
  let Q := R ^ (10 * B.card)
  let U := summandTail C (Q + N₀) N
  have hNU : ∀ a ∈ U, a ≤ N := fun a ha => (mem_summandTail C (Q + N₀) N a).mp ha |>.2.2
  let V := naturalIntervalSet U N
  have hcard : V.card = U.card := naturalIntervalSet_card U N hNU
  have hQsq : Q ^ 2 ≤ N := fixedShiftRoot_square_cutoff B.card N hB.card_pos
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ R))
  have hlog := nthRoot_log_comparison k N hk hN2 hR
  have hpow := pow_le_pow_left₀ hlogN hlog B.card
  rw [mul_pow] at hpow
  change Real.log (N : ℝ) ^ B.card ≤ F * Real.log (R : ℝ) ^ B.card at hpow
  by_cases hU : U.Nonempty
  · have hV : V.Nonempty := by rw [← Finset.card_pos, hcard]; exact hU.card_pos
    have hb := hN (N + 1) (by omega) V hV (by
      intro a ha
      have := (mem_summandTail C (Q + N₀) N a.val).mp (mem_naturalIntervalSet.mp ha)
      change Q < a.val
      omega) (by
      intro a ha b hb
      obtain ⟨haC, hlarge, _⟩ := (mem_summandTail C (Q + N₀) N a.val).mp
        (mem_naturalIntervalSet.mp ha)
      exact hprime a.val haC (by omega) b hb)
    rw [hcard] at hb
    change (U.card : ℝ) * Real.log (R : ℝ) ^ B.card ≤ D *
      (((N + 1 : ℕ) : ℝ) + (Q : ℝ) ^ 2) at hb
    have hsquare : (Q : ℝ) ^ 2 ≤ N := by exact_mod_cast hQsq
    have hb' : (U.card : ℝ) * Real.log (R : ℝ) ^ B.card ≤ D * (3 * (N : ℝ)) := by
      have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      push_cast at hb
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) U.card)
    have hf := mul_le_mul_of_nonneg_left hb' hF.le
    change (U.card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ _
    nlinarith
  · have hzero : U.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU)
    change (U.card : ℝ) * Real.log (N : ℝ) ^ B.card ≤ _
    rw [hzero, Nat.cast_zero, zero_mul]
    positivity

end Ostmann

end OAI
