import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertifiedRamseyReduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallCycleRamsey
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Triangle

namespace OAI

/-! Ramsey assembly separates finite coverage from the arithmetic,
small-cycle clauses, and least-order conclusion. -/

namespace CycleClique.Construction
/-- The finite obligation discharged by concrete certificate coverage. -/
def FiniteCertificateCoverage : Prop :=
  ∀ k t : ℕ, 5 ≤ k → k ≤ 17 → 3 ≤ t → t ≤ k → t ≤ 8 → k / 2 ≤ t →
    ∀ P ∈ pathPatterns t (k - t), HasCheckedCertificate k t P

theorem no_expanded_counterexample_of_finite_coverage (hCE : CEAlphaTwo)
    (hcoverage : FiniteCertificateCoverage)
    {V : Type} [Fintype V] {G : SimpleGraph V} {k a : ℕ}
    (hk : 5 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) : False := by
  have hcoverageAt : CertificateCoverageAt k := by
    intro t ht htk ht8 hhalf
    by_cases hk17 : k ≤ 17
    · exact hcoverage k t hk hk17 ht htk ht8 hhalf
    · have htk' : k / 2 ≤ 8 := hhalf.trans ht8
      omega
  exact no_expanded_counterexample_of_coverage hCE hcoverageAt hk ha hak hcard hI hcycle hexpand

theorem cycle_clique_upper_of_finite_coverage (hCE : CEAlphaTwo)
    (hcoverage : FiniteCertificateCoverage) {k a : ℕ}
    (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k) :
    RamseyProperty (k + 1) (a + 1) (k * a + 1) := by
  apply ramseyProperty_of_expanded_exclusion hk ha hak
  intro b hb hbk G hcycle hI hexpand
  by_cases hk3 : k = 3
  · subst k
    exact no_expanded_fourCycle_counterexample hb hbk (by simp) hI hcycle hexpand
  by_cases hk4 : k = 4
  · subst k
    exact no_expanded_fiveCycle_counterexample hb hbk (by simp) hI hcycle hexpand
  exact no_expanded_counterexample_of_finite_coverage hCE hcoverage (by omega) hb hbk (by simp) hI hcycle hexpand

theorem cycle_clique_main_of_finite_coverage (hCE : CEAlphaTwo)
    (hcoverage : FiniteCertificateCoverage) {m n : ℕ}
    (hn : 3 ≤ n) (hnm : n ≤ m) (hexcept : (m, n) ≠ (3, 3)) :
    IsRamseyNumber m n ((m - 1) * (n - 1) + 1) := by
  have hm4 : 4 ≤ m := by
    by_contra hm
    have hm3 : m = 3 := by omega
    have hn3 : n = 3 := by omega
    exact hexcept (by simp only [hm3, hn3])
  have hm' : m - 1 + 1 = m := by omega
  have hn' : n - 1 + 1 = n := by omega
  apply isRamseyNumber_of_upper_lower
  · simpa only [hm', hn'] using cycle_clique_upper_of_finite_coverage hCE hcoverage
      (k := m - 1) (a := n - 1) (by omega) (by omega) (by omega)
  · exact blockGraph_not_ramsey (by omega) (by omega)

theorem cycle_clique_ramsey_of_finite_coverage (hCE : CEAlphaTwo)
    (hcoverage : FiniteCertificateCoverage) {m n : ℕ}
    (hn : 3 ≤ n) (hnm : n ≤ m) :
    IsRamseyNumber m n (if m = 3 ∧ n = 3 then 6 else (m - 1) * (n - 1) + 1) := by
  by_cases hsmall : m = 3 ∧ n = 3
  · obtain ⟨rfl, rfl⟩ := hsmall
    simpa using triangle_ramsey
  · rw [ite_eq_right hsmall]
    apply cycle_clique_main_of_finite_coverage hCE hcoverage hn hnm
    intro he
    have hm : m = 3 := congrArg Prod.fst he
    have hn : n = 3 := congrArg Prod.snd he
    exact hsmall ⟨hm, hn⟩

end CycleClique.Construction

end OAI
