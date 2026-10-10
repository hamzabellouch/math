import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CanonicalRawCoverage
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteRangeReduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RamseyMainReduction

namespace OAI

/-! Mathematical assembly for a fixed cycle parameter, once its concrete
finite certificate coverage has been proved. -/

namespace CycleClique.Construction
open scoped Classical

def CertificateCoverageAt (k : ℕ) : Prop :=
  ∀ t, 3 ≤ t → t ≤ k → t ≤ 8 → k / 2 ≤ t →
    ∀ P ∈ pathPatterns t (k - t), HasCheckedCertificate k t P

theorem no_expanded_counterexample_of_coverage (hCE : CEAlphaTwo) {k : ℕ}
    (hcoverage : CertificateCoverageAt k)
    {V : Type} [Fintype V] {G : SimpleGraph V} {a : ℕ}
    (hk : 5 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) : False := by
  classical
  obtain ⟨_, hω3, hωhi, hhalf⟩ :=
    finite_range_clique_bounds hCE hk ha hak hcard hI hcycle hexpand
  obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
  have hQcard := hQ.card_eq
  have hQk : Q.card ≤ k := by omega
  obtain ⟨S, hopt⟩ := ExpandedPathSystem.exists_optimal G Q k
  obtain ⟨P, U, hP, hUv, hUa, hUe, hp, hne⟩ := hopt.exists_canonical_raw
  obtain ⟨n, c, hc⟩ := hcoverage Q.card (by omega) hQk (by omega) (by omega) P hP
  exact c.false_of_check hCE hk (by omega) hQk hQ.isClique hcycle (by omega)
    (fun I hi => (hI I hi).trans hak) hexpand hopt U hUv hUa hUe hp hne hc

theorem cycle_clique_upper_of_coverage (hCE : CEAlphaTwo) {k a : ℕ}
    (hk : 5 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k) (hcoverage : CertificateCoverageAt k) :
    RamseyProperty (k + 1) (a + 1) (k * a + 1) := by
  apply ramseyProperty_of_expanded_exclusion (by omega) ha hak
  intro b hb hbk G hcycle hI hexpand
  exact no_expanded_counterexample_of_coverage hCE hcoverage hk hb hbk (by simp) hI hcycle hexpand

theorem isRamseyNumber_of_certificate_coverage (hCE : CEAlphaTwo) {m n : ℕ}
    (hm : 6 ≤ m) (hn : 3 ≤ n) (hnm : n ≤ m)
    (hcoverage : CertificateCoverageAt (m - 1)) :
    IsRamseyNumber m n ((m - 1) * (n - 1) + 1) := by
  have hm' : m - 1 + 1 = m := by omega
  have hn' : n - 1 + 1 = n := by omega
  apply isRamseyNumber_of_upper_lower
  · simpa only [hm', hn'] using cycle_clique_upper_of_coverage hCE
      (k := m - 1) (a := n - 1) (by omega) (by omega) (by omega) hcoverage
  · exact blockGraph_not_ramsey (by omega) (by omega)

end CycleClique.Construction

end OAI
