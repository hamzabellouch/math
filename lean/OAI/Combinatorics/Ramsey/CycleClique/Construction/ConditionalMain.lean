import OAI.Combinatorics.Ramsey.CycleClique.Construction.AllCheckedCertificates
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RamseyFromFiniteCoverage

namespace OAI

/-! The full main Ramsey theorem, conditional only on the precisely stated
published Chvátal–Erdős input. Finite obstruction inputs are discharged by
kernel-checked concrete certificates and their exhaustive coverage. -/

namespace CycleClique.Construction
theorem finiteCertificateCoverage : FiniteCertificateCoverage :=
  fun _ _ hk hk' ht htk ht' hhalf => checked_certificate_coverage hk hk' ht htk ht' hhalf

theorem no_expanded_counterexample (hCE : CEAlphaTwo)
    {V : Type} [Fintype V] {G : SimpleGraph V} {k a : ℕ}
    (hk : 5 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) : False :=
  no_expanded_counterexample_of_finite_coverage hCE finiteCertificateCoverage
    hk ha hak hcard hI hcycle hexpand

theorem cycle_clique_upper (hCE : CEAlphaTwo) {k a : ℕ}
    (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k) :
    RamseyProperty (k + 1) (a + 1) (k * a + 1) :=
  cycle_clique_upper_of_finite_coverage hCE finiteCertificateCoverage hk ha hak

theorem cycle_clique_main (hCE : CEAlphaTwo) {m n : ℕ}
    (hn : 3 ≤ n) (hnm : n ≤ m) (hexcept : (m, n) ≠ (3, 3)) :
    IsRamseyNumber m n ((m - 1) * (n - 1) + 1) :=
  cycle_clique_main_of_finite_coverage hCE finiteCertificateCoverage hn hnm hexcept

theorem cycle_clique_ramsey (hCE : CEAlphaTwo) {m n : ℕ}
    (hn : 3 ≤ n) (hnm : n ≤ m) :
    IsRamseyNumber m n (if m = 3 ∧ n = 3 then 6 else (m - 1) * (n - 1) + 1) :=
  cycle_clique_ramsey_of_finite_coverage hCE finiteCertificateCoverage hn hnm

end CycleClique.Construction

end OAI
