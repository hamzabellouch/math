import OAI.Combinatorics.Ramsey.CycleClique.Construction.RamseyReduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.LowerBound

namespace OAI

/-! Assemble a Ramsey upper bound once the expanded counterexamples in
its fixed cycle-length parameter have been excluded. -/

namespace CycleClique.Construction
theorem ramseyProperty_of_expanded_exclusion {k a : ℕ}
    (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hexclude : ∀ b, 2 ≤ b → b ≤ k →
      ∀ G : SimpleGraph (Fin (k * b + 1)),
        ¬ HasCycle G (k + 1) → IndependenceBound G b →
        (∀ I : Finset (Fin (k * b + 1)), G.IsIndepSet (I : Set _) → I.Nonempty →
          k * I.card + 1 ≤ (closedNeighborhood G I).card) → False) :
    RamseyProperty (k + 1) (a + 1) (k * a + 1) := by
  classical
  by_contra hfail
  obtain ⟨b, G, hb, hbk, hcycle, hI, hexpand⟩ :=
    exists_minimal_counterexample hk ha hak hfail
  exact hexclude b hb hbk G hcycle hI hexpand

theorem isRamseyNumber_of_expanded_exclusion {m n : ℕ}
    (hm : 4 ≤ m) (hn : 3 ≤ n) (hnm : n ≤ m)
    (hexclude : ∀ b, 2 ≤ b → b ≤ m - 1 →
      ∀ G : SimpleGraph (Fin ((m - 1) * b + 1)),
        ¬ HasCycle G m → IndependenceBound G b →
        (∀ I : Finset (Fin ((m - 1) * b + 1)), G.IsIndepSet (I : Set _) → I.Nonempty →
          (m - 1) * I.card + 1 ≤ (closedNeighborhood G I).card) → False) :
    IsRamseyNumber m n ((m - 1) * (n - 1) + 1) := by
  have hm' : m - 1 + 1 = m := by omega
  have hn' : n - 1 + 1 = n := by omega
  apply isRamseyNumber_of_upper_lower
  · have hupper := ramseyProperty_of_expanded_exclusion (k := m - 1) (a := n - 1)
      (by omega) (by omega) (by omega) (by simpa only [hm'] using hexclude)
    simpa only [hm', hn'] using hupper
  · exact blockGraph_not_ramsey (by omega) (by omega)

end CycleClique.Construction

end OAI
