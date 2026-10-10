import OAI.Combinatorics.Ramsey.CycleClique.Construction.FullLargeClique
import OAI.Combinatorics.Ramsey.CycleClique.Construction.TerminalContradiction

namespace OAI

/-! After the proved large-clique contradiction, every remaining expanded
counterexample lies in the finite parameter range used by the certificates. -/

namespace CycleClique.Construction
open scoped Classical

theorem finite_range_clique_bounds (hCE : CEAlphaTwo)
    {V : Type} [Fintype V] {G : SimpleGraph V} {k a : ℕ}
    (hk : 5 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    k ≤ 17 ∧ 3 ≤ G.cliqueNum ∧ G.cliqueNum ≤ min k 8 ∧ k / 2 ≤ G.cliqueNum := by
  classical
  obtain ⟨hlo, hhi⟩ := large_clique_bounds (by omega) ha hak hcard hI hcycle hexpand
  have hsmall : G.cliqueNum ≤ 8 := by
    by_contra hn
    obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
    have hQcard := hQ.card_eq
    obtain ⟨S, hopt⟩ := ExpandedPathSystem.exists_optimal G Q k
    exact hopt.terminal_contradiction hCE (by omega) (by omega) (by omega)
      hQ.isClique hcycle (by omega) (fun I hi => (hI I hi).trans hak) hexpand
  omega

end CycleClique.Construction

end OAI
