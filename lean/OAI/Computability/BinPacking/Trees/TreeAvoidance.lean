import OAI.Computability.BinPacking.Trees.TreeColorCounts

namespace OAI

namespace BinPackingGap

def pullMarks (stem : List ℕ) (marks : Finset (List ℕ)) : Finset (List ℕ) :=
  (marks.filter (fun w => stem.IsPrefix w)).image (fun w => w.drop stem.length)

@[simp] theorem mem_pullMarks (stem word : List ℕ) (marks : Finset (List ℕ)) :
    word ∈ pullMarks stem marks ↔ stem ++ word ∈ marks := by
  constructor
  · intro hw
    obtain ⟨v, hv, hdrop⟩ := Finset.mem_image.mp hw
    obtain ⟨hvA, hpref⟩ := Finset.mem_filter.mp hv
    have heq : stem ++ word = v := by
      calc
        stem ++ word = stem ++ v.drop stem.length :=
          congrArg (fun t => stem ++ t) hdrop.symm
        _ = v.take stem.length ++ v.drop stem.length :=
          congrArg (fun t => t ++ v.drop stem.length) (List.prefix_iff_eq_take.mp hpref)
        _ = v := List.take_append_drop stem.length v
    exact heq.symm ▸ hvA
  · intro hw
    exact Finset.mem_image.mpr
      ⟨stem ++ word, Finset.mem_filter.mpr ⟨hw, List.prefix_append stem word⟩,
        by simp⟩

@[simp] theorem nil_mem_pullMarks (stem : List ℕ) (marks : Finset (List ℕ)) :
    [] ∈ pullMarks stem marks ↔ stem ∈ marks := by
  simpa only [List.append_nil] using mem_pullMarks stem [] marks

theorem levelCount_pullMarks_le (stem : List ℕ) (marks : Finset (List ℕ)) (j : ℕ) :
    levelCount (pullMarks stem marks) j ≤ levelCount marks (stem.length + j) := by
  have hsub : (pullMarks stem marks).filter (fun w => w.length = j) ⊆
      (marks.filter (fun w => w.length = stem.length + j)).image
        (fun w => w.drop stem.length) := by
    intro w hw
    obtain ⟨hw, hlen⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_image.mpr ⟨stem ++ w, ?_, by simp⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_pullMarks stem w marks).mp hw, by simp only [List.length_append, hlen]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem disjoint_prefixes_append_of_pull (stem word : List ℕ)
    (marks : Finset (List ℕ))
    (hold : Disjoint marks (UniformTree.prefixes stem))
    (hnew : Disjoint (pullMarks stem marks) (UniformTree.prefixes word)) :
    Disjoint marks (UniformTree.prefixes (stem ++ word)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hprefix
  rw [prefixes_append_eq] at hprefix
  rcases Finset.mem_union.mp hprefix with hprefix | hprefix
  · exact Finset.disjoint_left.mp hold hv hprefix
  · obtain ⟨w, _, hw, heq⟩ := mem_prefixesAfter_iff.mp hprefix
    apply Finset.disjoint_left.mp hnew
    · exact (mem_pullMarks stem w marks).mpr (heq.symm ▸ hv)
    · exact UniformTree.mem_prefixes_iff.mpr hw

def extendPhaseQuota (height : ℕ) (old : ℕ → ℕ) (depth : ℕ) : ℕ :=
  if depth ≤ height then old depth else phaseQuota (depth - height)

theorem extendPhaseQuota_old (height : ℕ) (old : ℕ → ℕ) {depth : ℕ}
    (hdepth : depth ≤ height) : extendPhaseQuota height old depth = old depth := by
  simp only [extendPhaseQuota, ite_eq_left hdepth]

theorem extendPhaseQuota_new (height : ℕ) (old : ℕ → ℕ) {j : ℕ}
    (hj : 0 < j) : extendPhaseQuota height old (height + j) = phaseQuota j := by
  have hnot : ¬ height + j ≤ height := by omega
  simp only [extendPhaseQuota, ite_eq_right hnot, Nat.add_sub_cancel_left]

theorem graft_avoids {n : ℕ} (old : AuxiliaryTree n)
    (G : old.tree.leaves → AuxiliaryTree 1) (N : ℕ)
    (hG : ∀ l, (G l).tree.height = N)
    (hquota : ∀ l, (G l).quota = phaseQuota)
    (marks : Finset (List ℕ))
    (hmarks : RespectsTreeQuota
      (UniformTree.graft old.tree (fun l => (G l).tree) N hG)
      (extendPhaseQuota old.tree.height old.quota) marks) :
    ∃ leaf ∈ (UniformTree.graft old.tree (fun l => (G l).tree) N hG).leaves,
      Disjoint marks (UniformTree.prefixes leaf) := by
  have hold : RespectsTreeQuota old.tree old.quota marks := by
    refine ⟨hmarks.1, ?_⟩
    intro j hj hbound
    have hglobal := hmarks.2 j hj (by
      change j ≤ old.tree.height + N
      omega)
    simpa only [extendPhaseQuota_old old.tree.height old.quota hbound] using hglobal
  obtain ⟨l, hl, havoidOld⟩ := old.avoids marks hold
  let oldLeaf : old.tree.leaves := ⟨l, hl⟩
  have hlocal : RespectsTreeQuota (G oldLeaf).tree (G oldLeaf).quota
      (pullMarks l marks) := by
    constructor
    · rw [nil_mem_pullMarks]
      intro hmarked
      exact Finset.disjoint_left.mp havoidOld hmarked
        (UniformTree.mem_prefixes_iff.mpr (List.prefix_refl l))
    · intro j hj hbound
      have hjpos : 0 < j := by omega
      have hlocalBound : j ≤ N := by simpa only [hG oldLeaf] using hbound
      have hglobal := hmarks.2 (old.tree.height + j) (by omega) (by
        change old.tree.height + j ≤ old.tree.height + N
        omega)
      have hpull := levelCount_pullMarks_le l marks j
      rw [old.tree.length_leaf l hl] at hpull
      rw [hquota oldLeaf]
      exact hpull.trans (by
        simpa only [extendPhaseQuota_new old.tree.height old.quota hjpos] using hglobal)
  obtain ⟨w, hw, havoidNew⟩ := (G oldLeaf).avoids (pullMarks l marks) hlocal
  refine ⟨l ++ w, ?_, disjoint_prefixes_append_of_pull l w marks havoidOld havoidNew⟩
  exact (UniformTree.mem_graft_leaves old.tree (fun l => (G l).tree) N hG).mpr
    ⟨oldLeaf, w, hw, rfl⟩

end BinPackingGap

end OAI
