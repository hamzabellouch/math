import OAI.Combinatorics.InfiniteMatroid.CorollaryModel

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

def Wave {α ι : Type*} (M : ι → Matroid α) (F : Set α)
    (W : Set α × (ι → Set α)) : Prop :=
  W.1 ⊆ F ∧ (∀ i, W.2 i ⊆ W.1) ∧
    (Pairwise fun i j ↦ Disjoint (W.2 i) (W.2 j)) ∧
    ∀ i, W.1 ⊆ (M i).closure (W.2 i)

theorem exists_maximal_wave {α ι : Type*} (M : ι → Matroid α) (F : Set α) :
    ∃ W, Maximal (Wave M F) W := by
  classical
  apply zorn_le₀ {W | Wave M F W}
  intro c hc hchain
  let U : Set α × (ι → Set α) :=
    (⋃ W : c, W.1.1, fun i ↦ ⋃ W : c, W.1.2 i)
  have hle : ∀ W ∈ c, W ≤ U := by
    intro W hW
    refine ⟨?_, fun i ↦ ?_⟩
    · exact subset_iUnion_of_subset ⟨W, hW⟩ Subset.rfl
    · exact subset_iUnion_of_subset ⟨W, hW⟩ Subset.rfl
  refine ⟨U, ?_, hle⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    exact (hc W.2).1 hx
  · intro i x hx
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    exact (hle W W.2).1 ((hc W.2).2.1 i hx)
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨W, hxW⟩ := mem_iUnion.mp hxi
    obtain ⟨V, hxV⟩ := mem_iUnion.mp hxj
    rcases hchain.total W.2 V.2 with hWV | hVW
    · exact disjoint_left.mp ((hc V.2).2.2.1 hij) (hWV.2 i hxW) hxV
    · exact disjoint_left.mp ((hc W.2).2.2.1 hij) hxW (hVW.2 j hxV)
  · intro i x hx
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    exact (M i).closure_mono ((hle W W.2).2 i) ((hc W.2).2.2.2 i hx)

lemma contractOnto_ground_sdiff {α : Type*} (M : Matroid α) (P : Set α) :
    contractOnto M (M.E \ P) = M ／ P := rfl

@[simp] lemma contractOnto_ground {α : Type*} (M : Matroid α) (C : Set α) :
    (contractOnto M C).E = C := rfl

lemma Wave.lift_contract {α ι : Type*} {M : ι → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W V : Set α × (ι → Set α)}
    (hW : Wave M F W) (hV : Wave (fun i ↦ M i ／ W.1) (F \ W.1) V) :
    Wave M F (W.1 ∪ V.1, fun i ↦ W.2 i ∪ V.2 i) := by
  refine ⟨union_subset hW.1 (hV.1.trans sdiff_subset), ?_, ?_, ?_⟩
  · intro i
    exact union_subset_union (hW.2.1 i) (hV.2.1 i)
  · intro i j hij
    apply disjoint_left.mpr
    rintro x (hxi | hxi) (hxj | hxj)
    · exact disjoint_left.mp (hW.2.2.1 hij) hxi hxj
    · exact (hV.1 (hV.2.1 j hxj)).2 (hW.2.1 i hxi)
    · exact (hV.1 (hV.2.1 i hxi)).2 (hW.2.1 j hxj)
    · exact disjoint_left.mp (hV.2.2.1 hij) hxi hxj
  · intro i
    have hP : W.1 ⊆ (M i).closure (W.2 i ∪ V.2 i) :=
      (hW.2.2.2 i).trans ((M i).closure_mono subset_union_left)
    have hT : V.2 i ⊆ (M i).closure (W.2 i ∪ V.2 i) := by
      intro x hx
      refine (M i).mem_closure_of_mem' (Or.inr hx) ?_
      rw [hE i]
      exact (hV.1 (hV.2.1 i hx)).1
    refine union_subset hP ?_
    have hv := hV.2.2.2 i
    rw [Matroid.contract_closure_eq] at hv
    exact (hv.trans sdiff_subset).trans
      ((M i).closure_subset_closure_of_subset_closure (union_subset hT hP))

lemma residual_wave_empty {α ι : Type*} {M : ι → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W V : Set α × (ι → Set α)}
    (hW : Maximal (Wave M F) W)
    (hV : Wave (fun i ↦ M i ／ W.1) (F \ W.1) V) : V.1 = ∅ := by
  have hLift := hW.1.lift_contract hE hV
  have hle : W ≤ (W.1 ∪ V.1, fun i ↦ W.2 i ∪ V.2 i) :=
    ⟨subset_union_left, fun _ ↦ subset_union_left⟩
  have hsub : V.1 ⊆ W.1 := subset_union_right.trans (hW.2 hLift hle).1
  exact eq_empty_iff_forall_notMem.mpr fun x hx ↦ (hV.1 hx).2 (hsub hx)

lemma wave_of_restriction_packing {α ι : Type*} {M : ι → Matroid α} {F Y : Set α}
    (hE : ∀ i, (M i).E = F) (hY : Y ⊆ F)
    (h : FamilyPacking (fun i ↦ M i ↾ Y)) :
    ∃ S, Wave M F (Y, S) := by
  obtain ⟨S, hdisj, hS⟩ := h
  have hSY : ∀ i, S i ⊆ Y := fun i ↦ (hS i).subset_ground
  refine ⟨S, hY, hSY, hdisj, fun i ↦ ?_⟩
  exact ((M i).restrict_spanning_iff (hSY i) (by rw [hE]; exact hY)).mp (hS i)

lemma FamilyCovering.empty {α ι : Type*} (M : ι → Matroid α) :
    FamilyCovering ∅ (fun i ↦ M i ↾ ∅) := by
  refine ⟨fun _ ↦ ∅, fun _ ↦ Matroid.empty_indep _, ?_⟩
  simp

lemma residual_covering_condition {α ι : Type*} {M : ι → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W : Set α × (ι → Set α)}
    (hW : Maximal (Wave M F) W) :
    ∀ Y ⊆ F \ W.1, FamilyPacking (fun i ↦ (M i ／ W.1) ↾ Y) →
      FamilyCovering Y (fun i ↦ (M i ／ W.1) ↾ Y) := by
  intro Y hY hpack
  have hg : ∀ i, (M i ／ W.1).E = F \ W.1 := by simp [hE]
  obtain ⟨S, hS⟩ := wave_of_restriction_packing hg hY hpack
  have hzero : Y = ∅ := residual_wave_empty hE hW hS
  subst Y
  exact FamilyCovering.empty _

end InfiniteMatroidCounterexample

end OAI
