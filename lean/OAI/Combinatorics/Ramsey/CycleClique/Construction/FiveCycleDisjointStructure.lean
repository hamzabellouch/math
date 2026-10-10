import OAI.Combinatorics.Ramsey.CycleClique.Construction.TriangleLabels

namespace OAI

/-! Disjoint triangle exterior classes are necessarily two-vertex cliques. -/

namespace CycleClique.Construction
theorem fiveCycle_disjoint_triangle_structure {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 3)
    (hcycle : ¬ HasCycle G 5) (hω : G.cliqueNum ≤ 3) (horder : Fintype.card V ≤ 17)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      4 * I.card + 1 ≤ (closedNeighborhood G I).card)
    (hdis : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y →
      Disjoint (exteriorNeighbors G Q x) (exteriorNeighbors G Q y))
    (q : Fin 3 → V) (hq : Function.Injective q) (hqQ : ∀ i, q i ∈ Q) :
    ∀ i, (exteriorNeighbors G Q (q i)).card = 2 ∧
      G.IsClique (exteriorNeighbors G Q (q i) : Set V) := by
  classical
  let U := fun i => exteriorNeighbors G Q (q i)
  let α := fun i => (G.induce (U i : Set V)).indepNum
  let C := fun i => exteriorClosedNeighborhood G Q (U i)
  have hlow : ∀ i, 2 ≤ (U i).card := by
    intro i
    have hs := hexpand {q i} (by simp) (by simp)
    simp only [Finset.card_singleton, Nat.mul_one] at hs
    have h := exteriorNeighbors_card_lower (hqQ i) hs
    rw [hQcard] at h
    change 5 ≤ 3 + (U i).card at h
    omega
  have hU : ∀ i, (U i).Nonempty := fun i => Finset.card_pos.mp (by have := hlow i; omega)
  have hpos : ∀ i, 1 ≤ α i := by
    intro i
    let : Nonempty (U i) := (hU i).to_subtype
    exact indepNum_pos_of_nonempty _
  have hcover : ∀ i u, u ∈ U i → ∀ x ∈ Q, G.Adj u x → x = q i := by
    intro i u hu x hx hux
    exact exterior_unique_clique_neighbor hdis (hqQ i) hu hx hux
  have hAQ : ∀ i, Disjoint (U i) Q := by
    intro i
    apply Finset.disjoint_left.mpr
    intro u hu huQ
    exact (mem_exteriorNeighbors.mp hu).2 huQ
  have hgrow : ∀ i, 4 * α i ≤ (C i).card := fun i =>
    one_clique_neighbor_expansion (hU i) (hAQ i) (hcover i) hexpand
  have hCdis : ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    exact fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ i) (hqQ j)
      (fun h => hij (hq h)) (fun _ h => h) (fun _ h => h)
      (hdis _ (hqQ i) _ (hqQ j) (fun h => hij (hq h)))
  have hsum := exterior_disjoint_sum_bound Finset.univ U (fun i _ j _ hij => hCdis i j hij)
  rw [hQcard] at hsum
  change 3 + ∑ i : Fin 3, (C i).card ≤ Fintype.card V at hsum
  have hsum' : (C 0).card + (C 1).card + (C 2).card ≤ 14 := by
    rw [Fin.sum_univ_three] at hsum
    omega
  have hα0 : α 0 ≤ 1 := by
    have := hgrow 0; have := hgrow 1; have := hgrow 2
    have := hpos 1; have := hpos 2
    omega
  have hα1 : α 1 ≤ 1 := by
    have := hgrow 0; have := hgrow 1; have := hgrow 2
    have := hpos 0; have := hpos 2
    omega
  have hα2 : α 2 ≤ 1 := by
    have := hgrow 0; have := hgrow 1; have := hgrow 2
    have := hpos 0; have := hpos 1
    omega
  have hα : ∀ i, α i ≤ 1 := by
    intro i
    fin_cases i
    · exact hα0
    · exact hα1
    · exact hα2
  intro i
  have hcomplete := complete_of_indepNum_le_one (hα i)
  have hclique : G.IsClique (U i : Set V) := by
    intro u hu v hv huv
    have h : (G.induce (U i : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [hcomplete]
      exact fun he => huv (congrArg Subtype.val he)
    exact h
  have hupper := exterior_clique_card_le_two (hqQ i) (fun _ h => h) hclique hω
  change (U i).card ≤ 2 at hupper
  have hUcard : (U i).card = 2 := by have := hlow i; omega
  exact ⟨hUcard, hclique⟩

end CycleClique.Construction

end OAI
