import OAI.Combinatorics.Ramsey.CycleClique.Construction.ExteriorCounts

namespace OAI

/-! A C5-free graph with singleton expansion cannot contain a four-clique at order at most 17. -/

namespace CycleClique.Construction
theorem exterior_unique_clique_neighbor {V : Type*} [Fintype V]
    {G : SimpleGraph V} {Q : Finset V}
    (hdis : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y →
      Disjoint (exteriorNeighbors G Q x) (exteriorNeighbors G Q y))
    {q u x : V} (hq : q ∈ Q) (hu : u ∈ exteriorNeighbors G Q q)
    (hx : x ∈ Q) (hux : G.Adj u x) : x = q := by
  by_contra hn
  have hu' : u ∈ exteriorNeighbors G Q x :=
    mem_exteriorNeighbors.mpr ⟨hux.symm, (mem_exteriorNeighbors.mp hu).2⟩
  exact Finset.disjoint_left.mp (hdis q hq x hx (Ne.symm hn)) hu hu'

theorem fiveCycle_fourClique_impossible {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hcycle : ¬ HasCycle G 5) (horder : Fintype.card V ≤ 17)
    (hexpand : ∀ v, 5 ≤ (closedNeighborhood G {v}).card)
    {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 4) : False := by
  classical
  let e : Fin 4 ≃ Q := (Finset.equivFinOfCardEq hQcard).symm
  let q : Fin 4 → V := fun i => (e i).val
  have hq : Function.Injective q := Subtype.val_injective.comp e.injective
  have hqQ : ∀ i, q i ∈ Q := fun i => (e i).property
  let U := fun i => exteriorNeighbors G Q (q i)
  have hdis : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y →
      Disjoint (exteriorNeighbors G Q x) (exteriorNeighbors G Q y) := by
    intro x hx y hy hxy
    exact fiveCycle_fourClique_exterior_disjoint hQ hQcard hcycle hx hy hxy
  have hU : ∀ i, (U i).Nonempty := by
    intro i
    have h := exteriorNeighbors_card_lower (hqQ i) (hexpand (q i))
    rw [hQcard] at h
    have hpos : 0 < (exteriorNeighbors G Q (q i)).card := by omega
    exact Finset.card_pos.mp hpos
  have hAQ : ∀ i, Disjoint (U i) Q := by
    intro i
    apply Finset.disjoint_left.mpr
    intro u hu huQ
    exact (mem_exteriorNeighbors.mp hu).2 huQ
  have hCdis : ∀ i j, i ≠ j → Disjoint (exteriorClosedNeighborhood G Q (U i))
      (exteriorClosedNeighborhood G Q (U j)) := by
    intro i j hij
    exact fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ i) (hqQ j)
      (fun he => hij (hq he)) (fun _ h => h) (fun _ h => h)
      (hdis _ (hqQ i) _ (hqQ j) (fun he => hij (hq he)))
  have hlower : ∀ i, 4 ≤ (exteriorClosedNeighborhood G Q (U i)).card := by
    intro i
    obtain ⟨u, hu⟩ := hU i
    have h := exterior_closed_expansion_bound (k := 4) (B := {q i}) (I := {u})
      (by simpa only [Finset.card_singleton] using hexpand u)
      (by simpa only [Finset.singleton_subset_iff] using hu) (hAQ i) (by
        intro v hv x hx hvx
        have heq : v = u := Finset.mem_singleton.mp hv
        subst v
        exact Finset.mem_singleton.mpr (exterior_unique_clique_neighbor hdis (hqQ i) hu hx hvx))
    simp only [Finset.card_singleton] at h
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (f := fun _ => 4) (g := fun i => (exteriorClosedNeighborhood G Q (U i)).card)
    (fun i _ => hlower i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hbound := exterior_disjoint_sum_bound Finset.univ U (fun i _ j _ hij => hCdis i j hij)
  simp only [hQcard] at hbound
  omega

end CycleClique.Construction

end OAI
