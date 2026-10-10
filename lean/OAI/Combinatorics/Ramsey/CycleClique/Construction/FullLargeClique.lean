import OAI.Combinatorics.Ramsey.CycleClique.Construction.BfsColouredCycle
import OAI.Combinatorics.Ramsey.CycleClique.Construction.BfsOneBranch
import OAI.Combinatorics.Ramsey.CycleClique.Construction.DenseSubgraph
import OAI.Combinatorics.Ramsey.CycleClique.Construction.LargeClique

namespace OAI

/-! The quantitative clique bound of manuscript Theorem `clq:bound`. -/

namespace CycleClique.Construction
private theorem dense_layer_forces_cycle {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {root : V} {Y : Finset V} {d s k : ℕ}
    (hs : 4 ≤ s) (hk : 2 * s ≤ k) (hk' : k ≤ 2 * s + 1)
    (hd : d ≤ s) (hcard : k ≤ Y.card)
    (hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d)
    (hconn : (G.induce (Y : Set V)).Connected)
    (hnonbip : ¬ (G.induce (Y : Set V)).IsBipartite) (hno : G.cliqueNum < s)
    (hdegree : ∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard)
    (hpair : ∀ a b : Y, a ≠ b → ¬ G.Adj a.val b.val →
      2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {a, b}).card) :
    HasCycle G (k + 1) := by
  obtain ⟨p, hp, hpd, c, χ, hχ, hcommon, hsplit⟩ :=
    exists_bfs_branch_partition (by omega) hlayer
  by_cases hpone : p = 1
  · subst p
    exact layer_cycle_of_one_predecessor (by omega) hk' hcard hpd hlayer hconn hdegree c hcommon
  · exact layer_cycle_of_two_branches hs hk hk' (by omega) (hpd.trans hd) hpd
      hlayer hconn hnonbip hno hdegree hpair c χ hχ hcommon hsplit

/-- Manuscript Theorem `clq:bound`, with expansion and exact forbidden cycle as hypotheses. -/
theorem large_clique_bounds {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G (k + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card) :
    max 3 (k / 2) ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  classical
  obtain ⟨htriangle, hupper⟩ := triangle_clique_bounds hk ha hak hcard hI hcycle
  refine ⟨?_, hupper⟩
  by_cases hk7 : k ≤ 7
  · omega
  · have hk8 : 8 ≤ k := by omega
    let s := k / 2
    have hs : 4 ≤ s := by dsimp [s]; omega
    have hks : 2 * s ≤ k := by dsimp [s]; omega
    have hks' : k ≤ 2 * s + 1 := by dsimp [s]; omega
    have hhalf : s ≤ G.cliqueNum := by
      by_contra hsmall
      have hno : G.cliqueNum < s := by omega
      have hIk : IndependenceBound G k := fun I hi => (hI I hi).trans hak
      let : Nonempty V := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
      let root : V := Classical.choice inferInstance
      by_cases heven : k = 2 * s
      · have hInd : IndependenceBound G (2 * s) := by simpa only [← heven] using hIk
        have hExp : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
            2 * s * I.card + 1 ≤ (closedNeighborhood G I).card := by
          simpa only [← heven] using hexpand
        obtain ⟨d, _, hds, Y, hYD, _, hconn, hnonbip, hYcard, hdegree, hpair⟩ :=
          dense_layer_interface_even hs hno hInd hExp root
        have hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d :=
          fun v hv => mem_distanceLayer.mp (hYD hv)
        exact hcycle (dense_layer_forces_cycle hs hks hks' hds (by omega) hlayer
          hconn hnonbip hno hdegree hpair)
      · have hodd : k = 2 * s + 1 := by omega
        have hInd : IndependenceBound G (2 * s + 1) := by simpa only [← hodd] using hIk
        have hExp : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
            (2 * s + 1) * I.card + 1 ≤ (closedNeighborhood G I).card := by
          simpa only [← hodd] using hexpand
        obtain ⟨d, _, hds, Y, hYD, _, hconn, hnonbip, hYcard, hdegree, hpair⟩ :=
          dense_layer_interface_odd hs hno hInd hExp root
        have hlayer : ∀ v ∈ Y, G.Reachable root v ∧ G.dist root v = d :=
          fun v hv => mem_distanceLayer.mp (hYD hv)
        exact hcycle (dense_layer_forces_cycle hs hks hks' hds (by omega) hlayer
          hconn hnonbip hno hdegree hpair)
    dsimp [s] at hhalf
    omega

end CycleClique.Construction

end OAI
