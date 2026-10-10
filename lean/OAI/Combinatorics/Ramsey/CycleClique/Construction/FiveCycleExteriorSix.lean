import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleDisjointStructure

namespace OAI

/-! Each two-vertex exterior clique has at least six vertices in its closed exterior neighbourhood. -/

namespace CycleClique.Construction
theorem fiveCycle_exterior_closed_six {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q A : Finset V} {q : V}
    (hA : A ⊆ exteriorNeighbors G Q q) (hclique : G.IsClique (A : Set V)) (hAcard : A.card = 2)
    (hcover : ∀ u ∈ A, ∀ x ∈ Q, G.Adj u x → x = q)
    (hexpand : ∀ v, 5 ≤ (closedNeighborhood G {v}).card)
    (hdis : ∀ T : Finset V, G.IsClique (T : Set V) → T.card = 3 →
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (exteriorNeighbors G T x) (exteriorNeighbors G T y)) :
    6 ≤ (exteriorClosedNeighborhood G Q A).card := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have huq := (mem_exteriorNeighbors.mp (hA hu)).1
  have hvq := (mem_exteriorNeighbors.mp (hA hv)).1
  let T : Finset V := {q, u, v}
  have hT : G.IsNClique 3 T := SimpleGraph.is3Clique_triple_iff.mpr ⟨huq, hvq, hclique hu hv huv⟩
  have hqT : q ∈ T := by simp [T]
  have huT : u ∈ T := by simp [T]
  have hvT : v ∈ T := by simp [T]
  have hAT : A ⊆ T := by
    have hpair : ({u, v} : Finset V) = A := Finset.eq_of_subset_of_card_le
      (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hu, hv⟩)
      (by rw [hAcard, Finset.card_pair huv])
    rw [← hpair]
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨huT, hvT⟩
  let B := exteriorNeighbors G T u
  let D := exteriorNeighbors G T v
  have hBD : Disjoint B D := hdis T hT.isClique hT.card_eq u huT v hvT huv
  have hBcard : 2 ≤ B.card := by
    have h := exteriorNeighbors_card_lower huT (hexpand u)
    rw [hT.card_eq] at h
    change 5 ≤ 3 + B.card at h
    omega
  have hDcard : 2 ≤ D.card := by
    have h := exteriorNeighbors_card_lower hvT (hexpand v)
    rw [hT.card_eq] at h
    change 5 ≤ 3 + D.card at h
    omega
  have hAQ : ∀ a ∈ A, a ∉ Q := fun a ha => (mem_exteriorNeighbors.mp (hA ha)).2
  have hBC : B ⊆ exteriorClosedNeighborhood G Q A := by
    intro z hz
    obtain ⟨huz, hzT⟩ := mem_exteriorNeighbors.mp hz
    apply mem_exteriorClosedNeighborhood.mpr
    refine ⟨Or.inr ⟨u, hu, huz⟩, ?_⟩
    intro hzQ
    exact hzT ((hcover u hu z hzQ huz).symm ▸ hqT)
  have hDC : D ⊆ exteriorClosedNeighborhood G Q A := by
    intro z hz
    obtain ⟨hvz, hzT⟩ := mem_exteriorNeighbors.mp hz
    apply mem_exteriorClosedNeighborhood.mpr
    refine ⟨Or.inr ⟨v, hv, hvz⟩, ?_⟩
    intro hzQ
    exact hzT ((hcover v hv z hzQ hvz).symm ▸ hqT)
  have hAC : A ⊆ exteriorClosedNeighborhood G Q A := fun a ha => mem_exteriorClosedNeighborhood.mpr ⟨Or.inl ha, hAQ a ha⟩
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzB
    exact (mem_exteriorNeighbors.mp hzB).2 (hAT hzA)
  have hAD : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro z hzA hzD
    exact (mem_exteriorNeighbors.mp hzD).2 (hAT hzA)
  have hsub : A ∪ (B ∪ D) ⊆ exteriorClosedNeighborhood G Q A :=
    Finset.union_subset hAC (Finset.union_subset hBC hDC)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨hAB, hAD⟩),
    Finset.card_union_of_disjoint hBD, hAcard] at hcount
  omega

end CycleClique.Construction

end OAI
