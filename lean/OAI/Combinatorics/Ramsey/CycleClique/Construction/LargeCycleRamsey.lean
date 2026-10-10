import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalContradiction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FullLargeClique
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RamseyMainReduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.LowerBound

namespace OAI

/-! The complete main formula for cycle length at least nineteen, conditional
on the precisely stated published Hamiltonicity input. No finite search is
needed in this range. -/

namespace CycleClique.Construction
open scoped Classical

theorem no_expanded_largeCycle_counterexample (hCE : CEAlphaTwo)
    {V : Type} [Fintype V] {G : SimpleGraph V} {k a : ℕ}
    (hk : 18 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) : False := by
  classical
  obtain ⟨hlo, hhi⟩ := large_clique_bounds (by omega) ha hak hcard hI hcycle hexpand
  obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
  have hQcard := hQ.card_eq
  have ht : 9 ≤ Q.card := by rw [hQ.card_eq]; omega
  have hQk : Q.card ≤ k := by omega
  have hkQ : k ≤ 2 * Q.card + 1 := by rw [hQ.card_eq]; omega
  obtain ⟨S, hopt⟩ := ExpandedPathSystem.exists_optimal G Q k
  exact hopt.terminal_contradiction hCE ht hQk hkQ hQ.isClique hcycle
    (by omega) (fun I hI' => (hI I hI').trans hak) hexpand

theorem cycle_clique_large_upper (hCE : CEAlphaTwo) {k a : ℕ}
    (hk : 18 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k) :
    RamseyProperty (k + 1) (a + 1) (k * a + 1) := by
  apply ramseyProperty_of_expanded_exclusion (by omega) ha hak
  intro b hb hbk G hcycle hI hexpand
  exact no_expanded_largeCycle_counterexample hCE hk hb hbk
    (by simp) hI hcycle hexpand

theorem cycle_clique_ge_nineteen (hCE : CEAlphaTwo) {m n : ℕ}
    (hm : 19 ≤ m) (hn : 3 ≤ n) (hnm : n ≤ m) :
    IsRamseyNumber m n ((m - 1) * (n - 1) + 1) := by
  have hm' : m - 1 + 1 = m := by omega
  have hn' : n - 1 + 1 = n := by omega
  apply isRamseyNumber_of_upper_lower
  · simpa only [hm', hn'] using
      cycle_clique_large_upper hCE (k := m - 1) (a := n - 1) (by omega) (by omega) (by omega)
  · exact blockGraph_not_ramsey (by omega) (by omega)

end CycleClique.Construction

end OAI
