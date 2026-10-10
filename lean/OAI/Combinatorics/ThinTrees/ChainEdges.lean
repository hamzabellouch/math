import OAI.Combinatorics.ThinTrees.HierarchyBuilder

namespace OAI

section

namespace StrongThinTree.MultiGraph.PartitionChain
noncomputable section
open Finset
variable {n m : ℕ} (P : PartitionChain n) (G : MultiGraph n m)

def block (i : ℕ) (v : Fin n) : Finset (Fin n) := (P.part_exists i v).choose
lemma block_mem (i : ℕ) (v : Fin n) : P.block i v ∈ P.parts i := (P.part_exists i v).choose_spec.1
lemma mem_block (i : ℕ) (v : Fin n) : v ∈ P.block i v := (P.part_exists i v).choose_spec.2
lemma block_eq_of_mem {i : ℕ} {A : Finset (Fin n)} (hA : A ∈ P.parts i) {v : Fin n} (hv : v ∈ A) :
    P.block i v=A := P.intersect_eq (P.block_mem i v) hA ⟨v,mem_inter.mpr ⟨P.mem_block i v,hv⟩⟩
lemma block_subset {i j : ℕ} (hij : i ≤ j) (v : Fin n) : P.block i v ⊆ P.block j v :=
  P.subset_of_intersect hij (P.block_mem i v) (P.block_mem j v)
    ⟨v,mem_inter.mpr ⟨P.mem_block i v,P.mem_block j v⟩⟩

def crossing (i : ℕ) : Finset (Fin m) := univ.filter (fun e => P.block i (G.left e) ≠ P.block i (G.right e))
lemma mem_crossing (i : ℕ) (e : Fin m) : e ∈ P.crossing G i ↔ P.block i (G.left e) ≠ P.block i (G.right e) := by
  simp [crossing]
lemma crossing_antitone : Antitone (P.crossing G) := by
  intro i j hij e he
  rw [P.mem_crossing] at he ⊢
  intro h
  apply he
  apply P.block_eq_of_mem (P.block_mem j (G.right e))
  exact P.block_subset hij (G.right e) (h ▸ P.mem_block i (G.left e))
lemma crossing_root {z : ℕ} (hz : P.parts z={univ}) : P.crossing G z=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have hl : P.block z (G.left e)=univ := mem_singleton.mp (hz ▸ P.block_mem z (G.left e))
  have hr : P.block z (G.right e)=univ := mem_singleton.mp (hz ▸ P.block_mem z (G.right e))
  exact (P.mem_crossing G z e).mp he (hl.trans hr.symm)

lemma cut_part_crossing {i : ℕ} {A : Finset (Fin n)} (hA : A ∈ P.parts i) :
    G.cut univ A ⊆ P.crossing G i := by
  intro e he
  rw [P.mem_crossing]
  intro h
  have hc := (mem_filter.mp he).2
  rcases hc with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · have hla := P.block_eq_of_mem hA hl
    exact hr ((h.symm.trans hla) ▸ P.mem_block i (G.right e))
  · have hra := P.block_eq_of_mem hA hr
    exact hl ((h.trans hra) ▸ P.mem_block i (G.left e))

lemma boundary_sum_le (i : ℕ) :
    ∑A ∈ P.parts i, (G.cut univ A).card ≤ 2*(P.crossing G i).card := by
  classical
  let C (e : Fin m) := (P.parts i).filter (fun A => e ∈ G.cut univ A)
  have hC (e : Fin m) : C e ⊆ {P.block i (G.left e),P.block i (G.right e)} := by
    intro A hA
    obtain ⟨hAP,he⟩ := mem_filter.mp hA
    rcases (mem_filter.mp he).2 with ⟨hl,_⟩ | ⟨hr,_⟩
    · exact mem_insert.mpr (Or.inl (P.block_eq_of_mem hAP hl).symm)
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (P.block_eq_of_mem hAP hr).symm))
  have hc (e : Fin m) : (C e).card ≤ if e ∈ P.crossing G i then 2 else 0 := by
    split_ifs with he
    · exact (card_le_card (hC e)).trans (by simpa using card_insert_le (P.block i (G.left e)) {P.block i (G.right e)})
    · have hem : C e=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro A hA
        obtain ⟨hAP,heA⟩ := mem_filter.mp hA
        exact he (P.cut_part_crossing G hAP heA)
      simp [hem]
  have heq : (∑A ∈ P.parts i, (G.cut univ A).card)=∑e : Fin m, (C e).card := by
    simp only [C,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    simp [cut]
  rw [heq]
  calc
    (∑e : Fin m, (C e).card) ≤ ∑e : Fin m, if e ∈ P.crossing G i then 2 else 0 := sum_le_sum (fun e _ => hc e)
    _ = 2*(P.crossing G i).card := by rw [←sum_filter]; simp [mul_comm]

lemma disappearing_in_parentBoundary {I : Finset ℕ} {H : Hierarchy n} (hH : H.nodes=P.nodes I)
    {i j : ℕ} (hi : i ∈ I) (hj : j ∈ I) (hij : i < j)
    (hnext : ∀k ∈ I, i < k → j ≤ k) {e : Fin m}
    (he : e ∈ P.crossing G i \ P.crossing G j) :
    ∃A ∈ P.parts i, e ∈ H.parentBoundary G A := by
  have he1 := (P.mem_crossing G i e).mp (mem_sdiff.mp he).1
  have he2 : P.block j (G.left e)=P.block j (G.right e) := by
    by_contra h
    exact (mem_sdiff.mp he).2 ((P.mem_crossing G j e).mpr h)
  have hr : G.right e ∉ P.block i (G.left e) := by
    intro hr
    exact he1 (P.block_eq_of_mem (P.block_mem i (G.left e)) hr).symm
  have hrB : G.right e ∈ P.block j (G.left e) := he2 ▸ P.mem_block j (G.right e)
  have hstrict : P.block i (G.left e) ⊂ P.block j (G.left e) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨P.block_subset hij.le _,?_⟩
    intro hh
    exact hr (hh ▸ hrB)
  have hparent := P.parent_at_transition hH hi hj hij hnext (P.block_mem i (G.left e)) (P.block_mem j (G.left e)) hstrict
  refine ⟨P.block i (G.left e),P.block_mem i _,?_⟩
  change e ∈ G.cut (G.inducedEdges (H.parent (P.block i (G.left e)))) (P.block i (G.left e))
  rw [hparent]
  exact mem_filter.mpr ⟨(G.mem_inducedEdges _ e).mpr ⟨P.mem_block j _,hrB⟩,Or.inl ⟨P.mem_block i _,hr⟩⟩

end
end StrongThinTree.MultiGraph.PartitionChain

end

end OAI
