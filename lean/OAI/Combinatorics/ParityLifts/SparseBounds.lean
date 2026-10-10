import OAI.Combinatorics.ParityLifts.SparseTree

namespace OAI

namespace ParityWL.Complexity

lemma cnf_card_bound {α : Type} [DecidableEq α] [Fintype α] (F : Sparsification.CNF α)
    (hw : ∀ C∈F, C.card≤3) : F.card≤4*(Fintype.card α+1)^3 := by
  classical
  have hs : F⊆(Finset.range 4).biUnion (fun i => (Finset.univ:Finset α).powersetCard i) := by
    intro C hC
    apply Finset.mem_biUnion.mpr
    exact ⟨C.card,Finset.mem_range.mpr (by have := hw C hC; omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,rfl⟩⟩
  calc
    F.card ≤ ((Finset.range 4).biUnion (fun i => (Finset.univ:Finset α).powersetCard i)).card := Finset.card_le_card hs
    _ ≤ ∑ i∈Finset.range 4, ((Finset.univ:Finset α).powersetCard i).card := Finset.card_biUnion_le
    _ = ∑ i∈Finset.range 4, (Fintype.card α).choose i := by simp
    _ ≤ ∑ _i∈Finset.range 4, (Fintype.card α+1)^3 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ Fintype.card α^i := Nat.choose_le_pow _ _
        _ ≤ (Fintype.card α+1)^i := Nat.pow_le_pow_left (by omega) _
        _ ≤ (Fintype.card α+1)^3 := Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by simp

/-- Finite-memory invariant: stored representatives, not just their sets. -/
def ClauseControlled {α : Type} [TreeCodec α] (S : ℕ) (C : List α) : Prop :=
  C.length≤3 ∧ ∀ a∈C, (treeEncode a).size≤S

def ListControlled {α : Type} [TreeCodec α] [DecidableEq α] (S : ℕ) (F : ClauseList α) : Prop :=
  (F.map List.toFinset).Nodup ∧ ∀ C∈F, ClauseControlled S C

lemma ClauseControlled.subset {α : Type} [TreeCodec α] {S : ℕ} {C D : List α}
    (hC : ClauseControlled S C) (hD : D.Sublist C) : ClauseControlled S D :=
  ⟨hD.length_le.trans hC.1,fun a ha => hC.2 a (hD.subset ha)⟩

lemma ListControlled.width {α : Type} [TreeCodec α] [DecidableEq α] {S : ℕ} {F : ClauseList α}
    (hF : ListControlled S F) : ∀ C∈listCNF F, C.card≤3 := by
  intro C hC
  obtain ⟨D,hD,rfl⟩ := mem_listCNF.mp hC
  exact (List.toFinset_card_le D).trans (hF.2 D hD).1

lemma ListControlled.size {α : Type} [TreeCodec α] [DecidableEq α] [Fintype α]
    {S : ℕ} {F : ClauseList α} (hF : ListControlled S F) :
    (treeEncode F).size ≤ 1+4*(Fintype.card α+1)^3*(2+3*(S+1)) := by
  have hlen : F.length=(listCNF F).card := by
    simpa [listCNF] using (List.toFinset_card_of_nodup hF.1).symm
  have hf := cnf_card_bound (listCNF F) hF.width
  rw [treeEncode_list_size]
  have hc : ∀ C∈F, (treeEncode C).size+1≤2+3*(S+1) := by
    intro C hC
    have hCC := hF.2 C hC
    rw [treeEncode_list_size]
    have hs := list_sum_map_le C (fun a => (treeEncode a).size+1) (S+1) (by
      intro a ha; have := hCC.2 a ha; omega)
    have hm := Nat.mul_le_mul_right (S+1) hCC.1
    omega
  have hs := list_sum_map_le F (fun C => (treeEncode C).size+1) (2+3*(S+1)) hc
  have hm := Nat.mul_le_mul_right (2+3*(S+1)) (show F.length≤4*(Fintype.card α+1)^3 by omega)
  omega

lemma compact_controlled {α : Type} [TreeCodec α] [DecidableEq α] (F : ClauseList α) (S : ℕ)
    (hF : ∀ C∈F, ClauseControlled S C) : ListControlled S (compactCNF F) :=
  ⟨dedupBy_nodup List.toFinset F,fun C hC => hF C (dedupBy_subset List.toFinset F hC)⟩

lemma minimize_controlled {α : Type} [TreeCodec α] [DecidableEq α] (F : ClauseList α) (S : ℕ)
    (hF : ∀ C∈F, ClauseControlled S C) : ListControlled S (minimizeList F) := by
  have hc := compact_controlled F S hF
  exact ⟨((List.filter_sublist (l:=compactCNF F)).map List.toFinset).nodup hc.1,
    fun C hC => hc.2 C (List.mem_filter.mp hC).1⟩

lemma prune_controlled {α : Type} [TreeCodec α] [DecidableEq α] (F A : ClauseList α) (S : ℕ)
    (hF : ∀ C∈F, ClauseControlled S C) (hA : ∀ C∈A, ClauseControlled S C) :
    ListControlled S (pruneList F A) := by
  apply compact_controlled
  intro C hC
  rcases List.mem_append.mp hC with hC | hC
  · exact hF C (List.mem_filter.mp hC).1
  · exact hA C hC

lemma selected_controlled {α : Type} [TreeCodec α] [DecidableEq α]
    (F : ClauseList α) (S p q h : ℕ) (hp : p≤3) (hF : ∀ C∈F, ClauseControlled S C)
    (hx : (flowerList F p q h).isEmpty≠true) :
    ClauseControlled S (selectedFlower F p q h).1 ∧
      ∀ P∈(selectedFlower F p q h).2, ClauseControlled S P := by
  have hm : selectedFlower F p q h∈flowerList F p q h := by
    unfold selectedFlower
    cases he : flowerList F p q h with
    | nil => simp [he] at hx
    | cons a as => simp
  obtain ⟨C,As,hC,hCF,hAs,hAF,he⟩ := (mem_flowerCandidates F p h _).mp ((mem_flowerList F p q h _).mp hm).1
  rw [he]
  refine ⟨⟨hC.trans_le hp,?_⟩,?_⟩
  · intro a ha
    obtain ⟨D,hD,haD⟩ := List.mem_flatten.mp (hCF ha)
    exact (hF D hD).2 a haD
  · intro P hP
    obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hP
    exact (hF D (hAF hD)).subset (List.filter_sublist)

lemma sparseStep_controlled {α : Type} [TreeCodec α] [DecidableEq α]
    {F : ClauseList α} {S : ℕ} (r : ℕ) (hF : ListControlled S F) :
    ListControlled S (sparseStep r F).2.1 ∧ ListControlled S (sparseStep r F).2.2 := by
  have branch (p q h : ℕ) (hp : p≤3) (hx : (flowerList F p q h).isEmpty≠true) :
      ListControlled S (sparseBranch F (selectedFlower F p q h)).2.1 ∧
      ListControlled S (sparseBranch F (selectedFlower F p q h)).2.2 := by
    obtain ⟨hc,hp⟩ := selected_controlled F S p q h hp hF.2 hx
    exact ⟨prune_controlled F _ S hF.2 (by intro C hC; simpa using (List.mem_singleton.mp hC) ▸ hc),
      prune_controlled F _ S hF.2 hp⟩
  unfold sparseStep
  split
  · split
    · split
      · exact ⟨hF,hF⟩
      · exact branch 1 2 _ (by omega) ‹_›
    · exact branch 2 1 _ (by omega) ‹_›
  · exact branch 1 1 _ (by omega) ‹_›

lemma SparseTree.controlled {α : Type} [TreeCodec α] [DecidableEq α]
    {r S : ℕ} (T : SparseTree α) (hT : T.Valid r) (hF : ListControlled S T.root) :
    T.All (ListControlled S) := by
  induction T with
  | leaf F => exact hF
  | branch F l t hl ht =>
    obtain ⟨_,hleft,hright,hlv,htv⟩ := hT
    have h := sparseStep_controlled r hF
    dsimp only [SparseTree.root] at h
    rw [hleft,hright] at h
    exact ⟨hF,hl hlv h.1,ht htv h.2⟩

end ParityWL.Complexity

end OAI
