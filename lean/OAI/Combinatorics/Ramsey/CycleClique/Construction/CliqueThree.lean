import OAI.Combinatorics.Ramsey.CycleClique.Construction.Size
import OAI.Combinatorics.Ramsey.CycleClique.Construction.LargeClique
import OAI.Combinatorics.Ramsey.CycleClique.Construction.LowerBound
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Monotonicity

namespace OAI

/-! The `n=3`, `m≥6` part of the formula, conditional on the same precise
published Hamiltonicity input as the size test. -/

namespace CycleClique.Construction
theorem cycle_clique_three_upper (hCE : CEAlphaTwo) {k : ℕ} (hk : 5 ≤ k) :
    RamseyProperty (k + 1) 3 (2 * k + 1) := by
  intro G
  by_cases hc : HasCycle G (k + 1)
  · exact Or.inl hc
  · apply Or.inr
    apply size_test_graph hCE hk (show 1 ≤ k by omega) hc
      (cliqueNum_le_of_no_cycle (by omega) hc)
    simp only [Fintype.card_fin]
    omega

theorem cycle_clique_three_ge_six (hCE : CEAlphaTwo) {m : ℕ} (hm : 6 ≤ m) :
    IsRamseyNumber m 3 ((m - 1) * 2 + 1) := by
  have hk : 5 ≤ m - 1 := by omega
  have hm' : m - 1 + 1 = m := by omega
  apply isRamseyNumber_of_upper_lower
  · simpa only [hm', Nat.mul_comm] using cycle_clique_three_upper hCE hk
  · simpa only [hm', Nat.mul_comm] using
      (blockGraph_not_ramsey (a := 2) (k := m - 1) (m := m) (n := 3)
        (by omega) (by omega))

end CycleClique.Construction

end OAI
