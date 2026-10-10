import OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachDenominator

namespace OAI

/-! The finite Goldbach upper bound with its denominator evaluated. -/

namespace TwoPointCorrelations

open Finset Problem337
open scoped Classical

lemma sieve_primesLE_card (z : ℕ) : (Nat.primesLE z).card ≤ z := by
  have hs : Nat.primesLE z ⊆ Icc 1 z := by
    intro p hp
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
  simpa using card_le_card hs

theorem sieve_goldbach_pairs_finite :
    ∃ C : ℝ, 0 < C ∧ ∀ N z : ℕ, 2 ∣ N → N ≠ 0 → 2 ≤ z →
      8 * (halaszMertensConstant + Real.log 2) ≤ Real.log z →
      ((PrimePairSieve.primePairs N).card : ℝ) ≤
        C * N * sieveSingularFactor N / Real.log z ^ 2 +
          (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z := by
  obtain ⟨c, hc, hden⟩ := sieve_goldbach_denominator_log_square
  refine ⟨1 / c, by positivity, ?_⟩
  intro N z hN hN0 hz hscale
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hS := sieve_singular_factor_pos N
  have hd := hden N z hN hN0 hz hscale
  have hmain : ((N - 1 : ℕ) : ℝ) / GoldbachSelberg.denominator N (primorial z) z ≤
      (1 / c) * N * sieveSingularFactor N / Real.log z ^ 2 := by
    calc
      _ ≤ (N : ℝ) / GoldbachSelberg.denominator N (primorial z) z := by
        apply div_le_div_of_nonneg_right _ (GoldbachSelberg.denominator_pos N (primorial z)
          hN (squarefree_primorial z) (by omega)).le
        exact_mod_cast Nat.sub_le N 1
      _ ≤ (N : ℝ) / (c * Real.log z ^ 2 / sieveSingularFactor N) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hd
      _ = _ := by field_simp
  have hp := GoldbachSelberg.primePairs_le_primorial N hN (z := z) (by omega)
  have hcard : ((Nat.primesLE z).card : ℝ) ≤ z := by exact_mod_cast sieve_primesLE_card z
  linarith

end TwoPointCorrelations

end OAI
