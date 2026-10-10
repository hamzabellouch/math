import OAI.Combinatorics.Ramsey.CycleClique.Construction.PublishedInputs
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Shortening

namespace OAI

/-!
# The manuscript's size test, conditional on Chvátal–Erdős

An induced vertex set larger than both `k` and twice the clique number
has an independent triple in a graph with no exact `(k + 1)`-cycle.
The only published hypothesis is `CEAlphaTwo`; the disconnected and
cutvertex cases and exact-cycle shortening are proved here.
-/

namespace CycleClique.Construction
private structure TwoCliquePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  cover : left ∪ right = Finset.univ
  disjoint : Disjoint left right
  left_clique : G.IsClique (left : Set V)
  right_clique : G.IsClique (right : Set V)
  anticomplete : ∀ x ∈ left, ∀ y ∈ right, ¬ G.Adj x y

private theorem two_clique_partition {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} (hi : ¬ HasIndependent G 3) (hn : ¬ G.Connected) :
    Nonempty (TwoCliquePartition G) := by
  classical
  have hnp : ¬ G.Preconnected := fun h => hn ⟨h⟩
  change ¬ ∀ u v, G.Reachable u v at hnp
  push Not at hnp
  obtain ⟨u, v, huv⟩ := hnp
  let A : Finset V := Finset.univ.filter (G.Reachable u)
  let B : Finset V := Finset.univ.filter (fun x => ¬ G.Reachable u x)
  have hcross : ∀ x ∈ A, ∀ y ∈ B, ¬ G.Adj x y := by
    intro x hx y hy hadj
    exact (Finset.mem_filter.mp hy).2 (((Finset.mem_filter.mp hx).2).trans hadj.reachable)
  have hA : G.IsClique (A : Set V) := by
    intro x hx y hy hxy
    by_contra hnxy
    have hxv : x ≠ v := by
      intro h; subst x; exact huv (Finset.mem_filter.mp hx).2
    have hyv : y ≠ v := by
      intro h; subst y; exact huv (Finset.mem_filter.mp hy).2
    have hv : v ∈ B := by simp [B, huv]
    exact hi (hasIndependent_three_of_distinct_nonadjacent hxy hxv hyv hnxy
      (hcross x hx v hv) (hcross y hy v hv))
  have hB : G.IsClique (B : Set V) := by
    intro x hx y hy hxy
    by_contra hnxy
    have hu : u ∈ A := by simp [A]
    have hxu : x ≠ u := by
      intro h; subst x; exact (Finset.mem_filter.mp hx).2 .rfl
    have hyu : y ≠ u := by
      intro h; subst y; exact (Finset.mem_filter.mp hy).2 .rfl
    exact hi (hasIndependent_three_of_distinct_nonadjacent hxy hxu hyu hnxy
      (fun h => hcross u hu x hx h.symm) (fun h => hcross u hu y hy h.symm))
  refine ⟨⟨A, B, ?_, ?_, hA, hB, hcross⟩⟩
  · ext x
    simp [A, B]
    exact Classical.em _
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2

private theorem TwoCliquePartition.card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (p : TwoCliquePartition G) :
    p.left.card + p.right.card = Fintype.card V := by
  classical
  rw [← Finset.card_union_of_disjoint p.disjoint, p.cover, Finset.card_univ]

private theorem connected_of_no_independent_triple {V : Type*} [Fintype V]
    {G : SimpleGraph V} {t : ℕ} (hi : ¬ HasIndependent G 3)
    (ht : G.cliqueNum ≤ t) (hcard : 2 * t < Fintype.card V) : G.Connected := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  by_contra hn
  obtain ⟨p⟩ := two_clique_partition hi hn
  have hA := p.left_clique.card_le_cliqueNum.trans ht
  have hB := p.right_clique.card_le_cliqueNum.trans ht
  have := p.card
  omega

private theorem joined_clique_card {V : Type*} [Fintype V] {G : SimpleGraph V}
    (v : V) (A : Finset {w : V | w ≠ v})
    (hA : (G.induce {w | w ≠ v}).IsClique (A : Set {w : V | w ≠ v}))
    (hjoin : ∀ a ∈ A, G.Adj v a.val) : A.card + 1 ≤ G.cliqueNum := by
  classical
  let A' : Finset V := A.map ⟨Subtype.val, Subtype.val_injective⟩
  have hA' : G.IsClique (A' : Set V) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hA ha hb (fun h => hxy (congrArg Subtype.val h))
  have hv : v ∉ A' := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
    exact a.property ha
  have hQ : G.IsClique ((insert v A' : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    apply hA'.insert
    intro x hx _
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    exact hjoin a ha
  simpa [Finset.card_insert_of_notMem hv, A'] using hQ.card_le_cliqueNum

private theorem deletion_connected_of_no_independent_triple {V : Type*} [Fintype V]
    {G : SimpleGraph V} {t : ℕ} (hi : ¬ HasIndependent G 3)
    (ht : G.cliqueNum ≤ t) (hcard : 2 * t < Fintype.card V)
    (htpos : 1 ≤ t) (v : V) : (G.induce {w | w ≠ v}).Connected := by
  classical
  let W := {w : V | w ≠ v}
  let H : SimpleGraph W := G.induce {w | w ≠ v}
  have hW : Fintype.card W = Fintype.card V - 1 := by
    change Fintype.card {w : V // ¬ w = v} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl]
    simp
  let : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hI : ¬ HasIndependent H 3 := fun h => hi (h.map Subtype.val Subtype.val_injective (fun h => h))
  by_contra hn
  obtain ⟨p⟩ := two_clique_partition hI hn
  have hH : H.cliqueNum ≤ t := (G.cliqueNum_induce_le _).trans ht
  have hA := p.left_clique.card_le_cliqueNum.trans hH
  have hB := p.right_clique.card_le_cliqueNum.trans hH
  have hsum := p.card
  have hAeq : p.left.card = t := by omega
  have hBeq : p.right.card = t := by omega
  have hjoin : (∀ a ∈ p.left, G.Adj v a.val) ∨ (∀ b ∈ p.right, G.Adj v b.val) := by
    by_cases hleft : ∀ a ∈ p.left, G.Adj v a.val
    · exact Or.inl hleft
    · right
      push Not at hleft
      obtain ⟨a, ha, hna⟩ := hleft
      intro b hb
      by_contra hnb
      have hab : a.val ≠ b.val := by
        intro h
        have heq : a = b := Subtype.ext h
        exact Finset.disjoint_left.mp p.disjoint ha (heq.symm ▸ hb)
      exact hi (hasIndependent_three_of_distinct_nonadjacent a.property.symm b.property.symm hab
        hna hnb (p.anticomplete a ha b hb))
  rcases hjoin with hjoin | hjoin
  · have h := (joined_clique_card v p.left p.left_clique hjoin).trans ht
    omega
  · have h := (joined_clique_card v p.right p.right_clique hjoin).trans ht
    omega

/-- The size test on the whole finite graph, conditional only on the
published Chvátal–Erdős input. -/
theorem size_test_graph (hCE : CEAlphaTwo) {V : Type} [Fintype V]
    {G : SimpleGraph V} {k t : ℕ} (hk : 5 ≤ k) (ht : 1 ≤ t)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    (hcard : max k (2 * t) < Fintype.card V) : HasIndependent G 3 := by
  classical
  by_contra hi
  have hcardk : k < Fintype.card V := (le_max_left _ _).trans_lt hcard
  have hcardt : 2 * t < Fintype.card V := (le_max_right _ _).trans_lt hcard
  have hconn := connected_of_no_independent_triple hi hclique hcardt
  have hdel := deletion_connected_of_no_independent_triple hi hclique hcardt ht
  have hham := hCE V G (by omega) hconn hdel hi
  exact hcycle (cycle_shorten_to (by omega) (by omega) hham hi)

/-- Manuscript Lemma `size:test`: every sufficiently large vertex set
contains three independent vertices. -/
theorem size_test (hCE : CEAlphaTwo) {V : Type} [Fintype V]
    {G : SimpleGraph V} {k t : ℕ} (hk : 5 ≤ k) (ht : 1 ≤ t)
    (hcycle : ¬ HasCycle G (k + 1)) (hclique : G.cliqueNum ≤ t)
    (Y : Finset V) (hY : max k (2 * t) < Y.card) :
    HasIndependent (G.induce (Y : Set V)) 3 := by
  classical
  apply size_test_graph hCE hk ht
  · intro hc
    exact hcycle (hc.map Subtype.val Subtype.val_injective (fun h => h))
  · exact (G.cliqueNum_induce_le _).trans hclique
  · simpa using hY

end CycleClique.Construction

end OAI
