import OAI.Combinatorics.Ramsey.CycleClique.Construction.RamseyMainReduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallFourCycle
import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallFiveCycle

namespace OAI

/-! The unconditional main formula for cycle lengths four and five. -/

namespace CycleClique.Construction
theorem cycle_clique_four_upper {a : ℕ} (ha : 2 ≤ a) (hak : a ≤ 3) :
    RamseyProperty 4 (a + 1) (3 * a + 1) := by
  apply ramseyProperty_of_expanded_exclusion (by omega) ha hak
  intro b hb hbk G hcycle hI hexpand
  exact no_expanded_fourCycle_counterexample hb hbk (by simp) hI hcycle hexpand

theorem cycle_clique_five_upper {a : ℕ} (ha : 2 ≤ a) (hak : a ≤ 4) :
    RamseyProperty 5 (a + 1) (4 * a + 1) := by
  apply ramseyProperty_of_expanded_exclusion (by omega) ha hak
  intro b hb hbk G hcycle hI hexpand
  exact no_expanded_fiveCycle_counterexample hb hbk (by simp) hI hcycle hexpand

theorem cycle_clique_four {n : ℕ} (hn : 3 ≤ n) (hnm : n ≤ 4) :
    IsRamseyNumber 4 n (3 * (n - 1) + 1) := by
  apply isRamseyNumber_of_upper_lower
  · have hn' : n - 1 + 1 = n := by omega
    simpa only [hn'] using cycle_clique_four_upper (a := n - 1) (by omega) (by omega)
  · exact blockGraph_not_ramsey (by omega) (by omega)

theorem cycle_clique_five {n : ℕ} (hn : 3 ≤ n) (hnm : n ≤ 5) :
    IsRamseyNumber 5 n (4 * (n - 1) + 1) := by
  apply isRamseyNumber_of_upper_lower
  · have hn' : n - 1 + 1 = n := by omega
    simpa only [hn'] using cycle_clique_five_upper (a := n - 1) (by omega) (by omega)
  · exact blockGraph_not_ramsey (by omega) (by omega)

end CycleClique.Construction

end OAI
