import OAI.Combinatorics.Ryser.Construction.ActualHypergraph
import OAI.Combinatorics.Ryser.Construction.GadgetExistence
import OAI.Combinatorics.Ryser.Field.ExtensionSubfields
import OAI.Combinatorics.Ryser.Hypergraph.Infinitude

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample

open Construction

theorem exists_prime_eventually_counterexampleRank :
    ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p % 3 = 2 ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n.Prime → 2 < n →
        CounterexampleRank (p ^ n + 1) := by
  classical
  obtain ⟨p, hp, hp5, hpmod, hgadget⟩ := exists_prime_goodGadget
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
  refine ⟨p, hp, hp5, hpmod, Q, ?_⟩
  intro n hQn hn hn3
  have hsize : Q ≤ Fintype.card (ExtensionField p n) := by
    rw [extensionField_card p n hn.ne_zero]
    have hnpow : n < p ^ n := Nat.lt_pow_self (by omega : 1 < p)
    exact hQn.trans hnpow.le
  have hsub : Incidence.SmallProperSubfields (ExtensionField p n) := by
    intro S hS
    exact extensionField_properSubfield_cube_le p n hn hn3 S hS
  obtain ⟨hgap, pool, hgood⟩ :=
    hpool (ExtensionField p n) (primeEmbedding p n) hsize hsub
  have hr := counterexampleRank_of_goodAmbientPool
    (primeEmbedding p n) u v huv hu hv a ha hcop K pool hgood hgap
  simpa only [extensionField_card p n hn.ne_zero] using hr

theorem infinite_counterexampleRanks : Set.Infinite {r : ℕ | CounterexampleRank r} := by
  obtain ⟨p, _hp, hp5, _hpmod, N, hexamples⟩ :=
    exists_prime_eventually_counterexampleRank
  exact infinite_counterexampleRanks_of_eventually_prime_powers
    p N (by omega) hexamples

end RyserCoveringCounterexample

end

end OAI
