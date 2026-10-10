import OAI.Combinatorics.Ryser.Hypergraph.Cover
import OAI.Combinatorics.Ryser.Hypergraph.Matching
import OAI.Combinatorics.Ryser.Hypergraph.Partite
import Mathlib.Data.Nat.Prime.Infinite

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

def CounterexampleRank (r : ℕ) : Prop :=
  ∃ (V : Type) (fin : Fintype V) (dec : DecidableEq V),
    letI : Fintype V := fin
    letI : DecidableEq V := dec
    ∃ H : Hypergraph V,
      0 < r ∧ H.Nonempty ∧ RPartiteUniform r H ∧ Intersecting H ∧
        (∃ C : Finset V, IsCover H C) ∧ matchingNumber H = 1 ∧ coverNumber H = r

theorem counterexampleRank_of_no_small_cover {V : Type} [Fintype V] [DecidableEq V]
    {r : ℕ} {H : Hypergraph V} (hr : 0 < r) (hne : H.Nonempty)
    (hpart : RPartiteUniform r H) (hI : Intersecting H)
    (hsmall : ∀ C : Finset V, C.card ≤ r - 1 → ¬ IsCover H C) :
    CounterexampleRank r := by
  refine ⟨V, inferInstance, inferInstance, H, hr, hne, hpart, hI, ?_, ?_, ?_⟩
  · exact (hpart.nonemptyEdges hr).exists_cover
  · exact matchingNumber_eq_one_of_nonempty_intersecting hne hI
  · exact coverNumber_eq_rank_of_no_small_cover hr hpart.uniform hne hI hsmall

theorem infinite_counterexampleRanks_of_unbounded
    (h : ∀ b : ℕ, ∃ r : ℕ, b < r ∧ CounterexampleRank r) :
    Set.Infinite {r : ℕ | CounterexampleRank r} := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨r, hbr, hr⟩ := h b
  exact (not_le_of_gt hbr) (hb hr)

theorem infinite_counterexampleRanks_of_eventually_prime_powers
    (s N : ℕ) (hs : 1 < s)
    (hexamples : ∀ n : ℕ, N ≤ n → Nat.Prime n → 2 < n →
      CounterexampleRank (s ^ n + 1)) :
    Set.Infinite {r : ℕ | CounterexampleRank r} := by
  apply infinite_counterexampleRanks_of_unbounded
  intro b
  obtain ⟨n, hn, hnprime⟩ := Nat.exists_infinite_primes (max N (max 3 (b + 1)))
  have hN : N ≤ n := (le_max_left N (max 3 (b + 1))).trans hn
  have hthree : 3 ≤ n :=
    ((le_max_left 3 (b + 1)).trans (le_max_right N (max 3 (b + 1)))).trans hn
  have hbn : b < n := Nat.lt_of_succ_le
    (((le_max_right 3 (b + 1)).trans (le_max_right N (max 3 (b + 1)))).trans hn)
  have hnpow : n < s ^ n := Nat.lt_pow_self hs
  refine ⟨s ^ n + 1, ?_, hexamples n hN hnprime (Nat.lt_of_succ_le hthree)⟩
  exact (hbn.trans hnpow).trans (Nat.lt_succ_self (s ^ n))

end RyserCoveringCounterexample

end

end OAI
