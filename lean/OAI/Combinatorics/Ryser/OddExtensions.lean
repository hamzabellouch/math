import OAI.Combinatorics.Ryser.Construction.OddGadgets
import OAI.Combinatorics.Ryser.Field.OddSubfields
import OAI.Combinatorics.Ryser.Hypergraph.Infinitude
import OAI.Combinatorics.Ryser.Construction.ActualHypergraph

namespace OAI

/-!
# Ryser counterexamples in all sufficiently large odd extension degrees

For every sufficiently large prime congruent to two modulo three, every
sufficiently large odd extension degree yields an intersecting partite uniform
hypergraph whose covering number equals its rank. The degree threshold may
depend on the prime. Infinitely many ranks occur; part sizes need not be equal.
-/

noncomputable section

namespace RyserOdd.Specification

open RyserCoveringCounterexample

/-- The base-prime threshold is uniform; the odd-degree threshold may depend
on the base prime. Every sufficiently large odd degree is included. -/
def EventualOddRanks : Prop :=
  ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → p % 3 = 2 →
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → Odd n →
      CounterexampleRank (p ^ n + 1)

/-- Infinitude refers to ranks of actual finite hypergraphs. -/
def InfiniteRanks : Prop :=
  Set.Infinite {r : ℕ | CounterexampleRank r}

/-- An actual finite partite uniform hypergraph witnessing strict failure
of Ryser's inequality. -/
def ExplicitFailureAt (r : ℕ) : Prop :=
  ∃ (V : Type) (fin : Fintype V) (dec : DecidableEq V),
    letI : Fintype V := fin
    letI : DecidableEq V := dec
    ∃ H : Hypergraph V,
      0 < r ∧ H.Nonempty ∧ RPartiteUniform r H ∧ Uniform r H ∧
        Intersecting H ∧ (∃ C : Finset V, IsCover H C) ∧
        matchingNumber H = 1 ∧ coverNumber H = r ∧
        (r - 1) * matchingNumber H < coverNumber H

/-- A counterexample rank yields a uniform hypergraph that strictly violates
Ryser's inequality. -/
theorem explicitFailureAt_of_counterexampleRank {r : ℕ}
    (hr : CounterexampleRank r) : ExplicitFailureAt r := by
  rcases hr with ⟨V, fin, dec, H, hpos, hne, hpart, hI, hcover, hmatch, hcard⟩
  let : Fintype V := fin
  let : DecidableEq V := dec
  refine ⟨V, fin, dec, H, hpos, hne, hpart, hpart.uniform, hI,
    hcover, hmatch, hcard, ?_⟩
  rw [hmatch, hcard, Nat.mul_one]
  exact Nat.sub_lt hpos (by decide)

/-- Eventual odd-degree counterexamples and infinitely many counterexample ranks,
without any requirement that the parts have equal size. -/
def WholeUnbalancedPaper : Prop := EventualOddRanks ∧ InfiniteRanks

end RyserOdd.Specification

namespace RyserOdd

open RyserCoveringCounterexample RyserCoveringCounterexample.Construction

theorem eventualOddRanks : Specification.EventualOddRanks := by
  classical
  obtain ⟨P, hP⟩ := exists_threshold_goodGadget
  refine ⟨P, ?_⟩
  intro p hpP hp hpmod
  obtain ⟨hp5, hgadget⟩ := hP p hpP hp hpmod
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hgadget
  have hs : 2 ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  obtain ⟨u, v, hu, hv, huv⟩ := exists_distinct_nonzero (k := ZMod p) (by
    rw [ZMod.card]
    omega)
  have hcop : Nat.Coprime 3 (Fintype.card (ZMod p) - 1) :=
    coprime_three_zmod_card_sub_one hpmod
  obtain ⟨K, Q, _hK, hpool⟩ :=
    exists_goodAmbientPool_uniform.{0, 0} u v huv a ha.1 hs
  refine ⟨max 3 Q, le_max_left _ _, ?_⟩
  intro n hn hnOdd
  have hn3 : 2 < n := lt_of_lt_of_le (by decide : 2 < 3)
    ((le_max_left 3 Q).trans hn)
  have hn0 : n ≠ 0 := by omega
  have hQn : Q ≤ n := (le_max_right 3 Q).trans hn
  have hsize : Q ≤ Fintype.card (ExtensionField p n) := by
    rw [extensionField_card p n hn0]
    have hnpow : n < p ^ n := Nat.lt_pow_self hp.one_lt
    exact hQn.trans hnpow.le
  have hsub : Incidence.SmallProperSubfields (ExtensionField p n) := by
    intro S hS
    exact extensionField_properSubfield_cube_le_of_odd p n hnOdd hn3 S hS
  obtain ⟨hgap, pool, hgood⟩ :=
    hpool (ExtensionField p n) (primeEmbedding p n) hsize hsub
  have hr := counterexampleRank_of_goodAmbientPool
    (primeEmbedding p n) u v huv hu hv a ha hcop K pool hgood hgap
  simpa only [extensionField_card p n hn0] using hr

theorem infiniteRanks : Specification.InfiniteRanks := by
  obtain ⟨P, hP⟩ := eventualOddRanks
  obtain ⟨p, hpP, hp, hpmod⟩ := exists_prime_gt_mod_three_eq_two P
  obtain ⟨N, _hN, hNall⟩ := hP p hpP.le hp hpmod
  apply infinite_counterexampleRanks_of_unbounded
  intro b
  let n := 2 * (N + b) + 1
  have hn : N ≤ n := by dsimp [n]; omega
  have hbn : b < n := by dsimp [n]; omega
  have hodd : Odd n := ⟨N + b, by dsimp [n]⟩
  have hnpow : n < p ^ n := Nat.lt_pow_self hp.one_lt
  exact ⟨p ^ n + 1, (hbn.trans hnpow).trans (Nat.lt_succ_self _), hNall n hn hodd⟩

theorem eventualExplicitFailures :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime → p % 3 = 2 →
      ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n → Odd n →
        Specification.ExplicitFailureAt (p ^ n + 1) := by
  obtain ⟨P, hP⟩ := eventualOddRanks
  refine ⟨P, ?_⟩
  intro p hpP hp hpmod
  obtain ⟨N, hN, hall⟩ := hP p hpP hp hpmod
  exact ⟨N, hN, fun n hn hnOdd =>
    Specification.explicitFailureAt_of_counterexampleRank (hall n hn hnOdd)⟩

theorem full_main : Specification.WholeUnbalancedPaper :=
  ⟨eventualOddRanks, infiniteRanks⟩

theorem eventualOddFailures_and_infinite :
    (∃ primeThreshold : ℕ, ∀ prime : ℕ, primeThreshold ≤ prime →
      prime.Prime → prime % 3 = 2 →
      ∃ degreeThreshold : ℕ, 3 ≤ degreeThreshold ∧
        ∀ degree : ℕ, degreeThreshold ≤ degree → Odd degree →
          Specification.ExplicitFailureAt (prime ^ degree + 1)) ∧
    Set.Infinite {rank : ℕ | Specification.ExplicitFailureAt rank} := by
  refine ⟨eventualExplicitFailures, ?_⟩
  exact infiniteRanks.mono fun _rank => Specification.explicitFailureAt_of_counterexampleRank

end RyserOdd

namespace RyserOddReference

theorem challenge : RyserOdd.Specification.WholeUnbalancedPaper :=
  RyserOdd.full_main

end RyserOddReference

end

end OAI
