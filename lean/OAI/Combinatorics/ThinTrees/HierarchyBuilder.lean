import OAI.Combinatorics.ThinTrees.PartitionRank

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n : ℕ}

namespace Hierarchy

theorem exists_structure (N : Finset (Finset (Fin n)))
    (hne : ∀A ∈ N, A.Nonempty) (hroot : univ ∈ N)
    (hleaf : ∀v, {v} ∈ N)
    (hlam : ∀A ∈ N, ∀B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) :
    ∃ H : Hierarchy n, H.nodes=N := by
  classical
  have hp (A : Finset (Fin n)) (hA : A ∈ N) (hAr : A ≠ univ) :
      ∃B ∈ N, A ⊂ B ∧ ∀C ∈ N, A ⊂ C → B ⊆ C := by
    let U := N.filter (fun B => A ⊂ B)
    have hu : univ ∈ U := mem_filter.mpr ⟨hroot,
      Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hAr⟩⟩
    obtain ⟨B,hB,hmin⟩ := exists_min_image U card ⟨univ,hu⟩
    obtain ⟨hBN,hAB⟩ := mem_filter.mp hB
    refine ⟨B,hBN,hAB,?_⟩
    intro C hCN hAC
    rcases hlam B hBN C hCN with hBC | hCB | hd
    · exact hBC
    · have hc : C ∈ U := mem_filter.mpr ⟨hCN,hAC⟩
      exact (eq_of_subset_of_card_le hCB (hmin C hc)).symm.subset
    · obtain ⟨a,ha⟩ := hne A hA
      exact False.elim (disjoint_left.mp hd (hAB.subset ha) (hAC.subset ha))
  let par (A : Finset (Fin n)) := if h : A ∈ N ∧ A ≠ univ then (hp A h.1 h.2).choose else univ
  have hs (A : Finset (Fin n)) (hA : A ∈ N) (hAr : A ≠ univ) :
      par A ∈ N ∧ A ⊂ par A ∧ ∀C ∈ N, A ⊂ C → par A ⊆ C := by
    dsimp [par]
    rw [dite_eq_left ⟨hA,hAr⟩]
    exact (hp A hA hAr).choose_spec
  exact ⟨⟨N,hne,hroot,hleaf,hlam,par,
    fun A hA hAr => (hs A hA hAr).1,
    fun A hA hAr => (hs A hA hAr).2.1,
    fun A hA hAr => (hs A hA hAr).2.2⟩,rfl⟩
end Hierarchy

structure PartitionChain (n : ℕ) where
  parts : ℕ → Finset (Finset (Fin n))
  partition : ∀i, VertexPartition univ (parts i)
  coarsens : ∀i j, i ≤ j → ∀A ∈ parts i, ∃B ∈ parts j, A ⊆ B

namespace PartitionChain
variable (P : PartitionChain n)
lemma parts_nonempty {i : ℕ} {A : Finset (Fin n)} (hA : A ∈ P.parts i) : A.Nonempty :=
  ((P.partition i).1 A hA).1

lemma parts_disjoint {i : ℕ} {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts i) (hne : A ≠ B) : Disjoint A B :=
  (P.partition i).2.1 hA hB hne

lemma part_exists (i : ℕ) (v : Fin n) : ∃A ∈ P.parts i, v ∈ A := by
  have hv : v ∈ (P.parts i).biUnion id := (P.partition i).2.2.symm ▸ mem_univ v
  exact mem_biUnion.mp hv

lemma intersect_eq {i : ℕ} {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts i) (hab : (A ∩ B).Nonempty) : A=B := by
  by_contra h
  exact hab.ne_empty (disjoint_iff_inter_eq_empty.mp (P.parts_disjoint hA hB h))

lemma subset_of_intersect {i j : ℕ} (hij : i ≤ j) {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts j) (hab : (A ∩ B).Nonempty) : A ⊆ B := by
  obtain ⟨C,hC,hAC⟩ := P.coarsens i j hij A hA
  have hCB : (C ∩ B).Nonempty := by
    obtain ⟨v,hv⟩ := hab
    exact ⟨v,mem_inter.mpr ⟨hAC (mem_inter.mp hv).1,(mem_inter.mp hv).2⟩⟩
  exact P.intersect_eq hC hB hCB ▸ hAC

lemma laminar {i j : ℕ} {A B : Finset (Fin n)}
    (hA : A ∈ P.parts i) (hB : B ∈ P.parts j) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  by_cases hd : Disjoint A B
  · exact Or.inr (Or.inr hd)
  have he := not_disjoint_iff_nonempty_inter.mp hd
  rcases le_total i j with hij | hji
  · exact Or.inl (P.subset_of_intersect hij hA hB he)
  · exact Or.inr (Or.inl (P.subset_of_intersect hji hB hA (by simpa [inter_comm] using he)))

def nodes (I : Finset ℕ) : Finset (Finset (Fin n)) :=
  I.biUnion P.parts ∪ univ.image (fun v : Fin n => {v})

lemma mem_nodes {I : Finset ℕ} {A : Finset (Fin n)} :
    A ∈ P.nodes I ↔ (∃i ∈ I, A ∈ P.parts i) ∨ ∃v, A={v} := by
  simp only [nodes,mem_union,mem_biUnion,mem_image,mem_univ,true_and]
  constructor
  · rintro (h | ⟨v,hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v,hv.symm⟩
  · rintro (h | ⟨v,hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v,hv.symm⟩

lemma nodes_nonempty {I : Finset ℕ} {A : Finset (Fin n)} (hA : A ∈ P.nodes I) : A.Nonempty := by
  rcases P.mem_nodes.mp hA with ⟨i,_,hi⟩ | ⟨v,rfl⟩
  · exact P.parts_nonempty hi
  · exact singleton_nonempty _

lemma nodes_laminar (I : Finset ℕ) : ∀A ∈ P.nodes I, ∀B ∈ P.nodes I,
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  intro A hA B hB
  rcases P.mem_nodes.mp hA with ⟨i,_,hi⟩ | ⟨v,rfl⟩ <;>
    rcases P.mem_nodes.mp hB with ⟨j,_,hj⟩ | ⟨w,rfl⟩
  · exact P.laminar hi hj
  · by_cases h : w ∈ A
    · exact Or.inr (Or.inl (singleton_subset_iff.mpr h))
    · exact Or.inr (Or.inr (disjoint_singleton_right.mpr h))
  · by_cases h : v ∈ B
    · exact Or.inl (singleton_subset_iff.mpr h)
    · exact Or.inr (Or.inr (disjoint_singleton_left.mpr h))
  · by_cases h : v=w
    · exact Or.inl (h ▸ Subset.rfl)
    · exact Or.inr (Or.inr (disjoint_singleton.mpr h))

lemma exists_hierarchy (I : Finset ℕ) (hroot : ∃i ∈ I, univ ∈ P.parts i) :
    ∃H : Hierarchy n, H.nodes=P.nodes I := by
  apply Hierarchy.exists_structure (P.nodes I)
  · exact fun A hA => P.nodes_nonempty hA
  · exact P.mem_nodes.mpr (Or.inl hroot)
  · intro v; exact P.mem_nodes.mpr (Or.inr ⟨v,rfl⟩)
  · exact P.nodes_laminar I

lemma parent_at_transition {I : Finset ℕ} {H : Hierarchy n} (hH : H.nodes=P.nodes I)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (_hij : i < j)
    (hnext : ∀k ∈ I, i < k → j ≤ k)
    {A B : Finset (Fin n)} (hA : A ∈ P.parts i) (hB : B ∈ P.parts j) (hAB : A ⊂ B) :
    H.parent A=B := by
  have hAN : A ∈ H.nodes := hH ▸ P.mem_nodes.mpr (Or.inl ⟨i,hi,hA⟩)
  have hBN : B ∈ H.nodes := hH ▸ P.mem_nodes.mpr (Or.inl ⟨j,hj,hB⟩)
  have hAr : A ≠ univ := fun h => (not_ssubset_of_subset (subset_univ _)) (h ▸ hAB)
  have hpB := H.parent_minimal A hAN hAr B hBN hAB
  have hAp := H.parent_strict A hAN hAr
  apply Subset.antisymm hpB
  have hpN : H.parent A ∈ P.nodes I := hH ▸ H.parent_mem A hAN hAr
  rcases P.mem_nodes.mp hpN with ⟨k,hk,hp⟩ | ⟨v,hp⟩
  · have hik : i < k := by
      by_contra h
      have hki : k ≤ i := by omega
      have hin : (H.parent A ∩ A).Nonempty := by
        obtain ⟨v,hv⟩ := P.parts_nonempty hA
        exact ⟨v,mem_inter.mpr ⟨hAp.subset hv,hv⟩⟩
      have he := P.subset_of_intersect hki hp hA hin
      exact (not_ssubset_of_subset he) hAp
    apply P.subset_of_intersect (hnext k hk hik) hB hp
    obtain ⟨v,hv⟩ := P.parts_nonempty hA
    exact ⟨v,mem_inter.mpr ⟨hAB.subset hv,hAp.subset hv⟩⟩
  · have hc := card_lt_card hAp
    rw [hp,card_singleton] at hc
    have hn := card_pos.mpr (P.parts_nonempty hA)
    omega

end PartitionChain
end
end StrongThinTree.MultiGraph

end

end OAI
