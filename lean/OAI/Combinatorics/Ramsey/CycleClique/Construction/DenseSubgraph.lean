import OAI.Combinatorics.Ramsey.CycleClique.Construction.DenseLayers

namespace OAI

/-!
# The dense layer interface

This assembles the minimum-order choice, connectivity, nonbipartiteness,
minimum degree, and independent-pair expansion. These are exactly the
properties used in the path argument in manuscript Section 3.
-/

namespace CycleClique.Construction
theorem independent_pair_finset {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
    (hxy : ¬ G.Adj x y) : G.IsIndepSet (({x, y} : Finset V) : Set V) := by
  classical
  intro a ha b hb hne hadj
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hne rfl
  · exact hxy hadj
  · exact hxy hadj.symm
  · exact hne rfl

theorem complete_of_indepNum_le_one {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hα : G.indepNum ≤ 1) : G = ⊤ := by
  classical
  apply SimpleGraph.isClique_univ.mp
  intro x _ y _ hxy
  by_contra hn
  have h := (independent_pair_finset hn).card_le_indepNum
  simp only [Finset.card_pair hxy] at h
  omega

theorem dense_indepNum_two {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s : ℕ}
    (hclique : G.cliqueNum < s) (hdense : s * G.indepNum ≤ Fintype.card V) :
    2 ≤ G.indepNum := by
  classical
  have hpos := indepNum_pos_of_nonempty G
  by_contra hn
  have htop := complete_of_indepNum_le_one (G := G) (by omega)
  have hfull : G.IsClique ((Finset.univ : Finset V) : Set V) := by rw [htop]; simp
  have hc := hfull.card_le_cliqueNum
  simp only [Finset.card_univ] at hc
  have hmul := Nat.mul_le_mul_left s hpos
  simp only [Nat.mul_one] at hmul
  omega

/-- Full even-parameter layer interface. -/
theorem dense_layer_interface_even {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s : ℕ} (hs : 4 ≤ s)
    (hclique : G.cliqueNum < s) (hInd : IndependenceBound G (2 * s))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      2 * s * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ ∃ Y : Finset V,
      Y ⊆ distanceLayer G root i ∧ Y.Nonempty ∧
      (G.induce (Y : Set V)).Connected ∧
      ¬ (G.induce (Y : Set V)).IsBipartite ∧ 2 * s ≤ Y.card ∧
      (∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard) ∧
      (∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
        2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {u, v}).card) := by
  classical
  obtain ⟨i, hi, his, hD, hdense⟩ := exists_dense_distance_layer_even
    (by omega) hInd hexpand root
  obtain ⟨Y, hYD, hYne, hYdense, hYmin⟩ := exists_minimal_dense_even _ hD hdense
  let : Nonempty Y := hYne.to_subtype
  let H := G.induce (Y : Set V)
  have hcard : Fintype.card Y = Y.card := Fintype.card_coe _
  have hdense' : s * H.indepNum ≤ Fintype.card Y := by simpa [hcard] using hYdense
  have hmin : ∀ Z : Finset Y, Z.Nonempty → Z.card < Fintype.card Y →
      Z.card < s * (H.induce (Z : Set Y)).indepNum := by
    simpa only [hcard] using hYmin
  have hconn := minimal_dense_connected_even hdense' hmin
  have hnonbip := dense_nonbipartite (by omega) hdense'
  have hHclique : H.cliqueNum < s := (G.cliqueNum_induce_le _).trans_lt hclique
  have hα := dense_indepNum_two hHclique hdense'
  have horder : 2 * s ≤ Fintype.card Y := by nlinarith
  have hdegree : ∀ v : Y, s ≤ (H.neighborSet v).ncard := by
    apply dense_expansion_degree (by omega) horder
    intro v hv
    have h := (minimal_dense_expansion_even hdense' hmin {v} (by simp) (by simp)).2 hv
    simpa using h
  have hpair : ∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
      2 * s ≤ (closedNeighborhood H {u, v}).card := by
    intro u v huv hnot
    have h := (minimal_dense_expansion_even hdense' hmin {u, v}
      (independent_pair_finset hnot) (by simp)).1
    simpa only [Finset.card_pair huv, Nat.mul_comm s 2] using h
  refine ⟨i, hi, his, Y, hYD, hYne, hconn, hnonbip, ?_, hdegree, hpair⟩
  simpa only [hcard] using horder

/-- Full odd-parameter layer interface. -/
theorem dense_layer_interface_odd {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s : ℕ} (hs : 4 ≤ s)
    (hclique : G.cliqueNum < s) (hInd : IndependenceBound G (2 * s + 1))
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      (2 * s + 1) * I.card + 1 ≤ (closedNeighborhood G I).card) (root : V) :
    ∃ i, 1 ≤ i ∧ i ≤ s ∧ ∃ Y : Finset V,
      Y ⊆ distanceLayer G root i ∧ Y.Nonempty ∧
      (G.induce (Y : Set V)).Connected ∧
      ¬ (G.induce (Y : Set V)).IsBipartite ∧ 2 * s + 1 ≤ Y.card ∧
      (∀ v : Y, s ≤ ((G.induce (Y : Set V)).neighborSet v).ncard) ∧
      (∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
        2 * s ≤ (closedNeighborhood (G.induce (Y : Set V)) {u, v}).card) := by
  classical
  obtain ⟨i, hi, his, hD, hdense⟩ := exists_dense_distance_layer_odd
    (by omega) hInd hexpand root
  obtain ⟨Y, hYD, hYne, hYdense, hYmin⟩ := exists_minimal_dense_odd _ hD hdense
  let : Nonempty Y := hYne.to_subtype
  let H := G.induce (Y : Set V)
  have hcard : Fintype.card Y = Y.card := Fintype.card_coe _
  have hdense' : s * H.indepNum < Fintype.card Y := by simpa [hcard] using hYdense
  have hmin : ∀ Z : Finset Y, Z.Nonempty → Z.card < Fintype.card Y →
      Z.card ≤ s * (H.induce (Z : Set Y)).indepNum := by
    simpa only [hcard] using hYmin
  have hconn := minimal_dense_connected_odd hdense' hmin
  have hnonbip := dense_nonbipartite (by omega) hdense'.le
  have hHclique : H.cliqueNum < s := (G.cliqueNum_induce_le _).trans_lt hclique
  have hα := dense_indepNum_two hHclique hdense'.le
  have horder : 2 * s + 1 ≤ Fintype.card Y := by nlinarith
  have hdegree : ∀ v : Y, s ≤ (H.neighborSet v).ncard := by
    apply dense_expansion_degree (by omega) (by omega)
    intro v _
    have h := minimal_dense_expansion_odd hdense' hmin {v} (by simp) (by simp)
    simpa using h
  have hpair : ∀ u v : Y, u ≠ v → ¬ G.Adj u.val v.val →
      2 * s ≤ (closedNeighborhood H {u, v}).card := by
    intro u v huv hnot
    have h := minimal_dense_expansion_odd hdense' hmin {u, v}
      (independent_pair_finset hnot) (by simp)
    simp only [Finset.card_pair huv, Nat.mul_comm s 2] at h
    omega
  refine ⟨i, hi, his, Y, hYD, hYne, hconn, hnonbip, ?_, hdegree, hpair⟩
  simpa only [hcard] using horder

end CycleClique.Construction

end OAI
