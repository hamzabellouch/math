import OAI.Computability.BinPacking.Trees.IntegerTreeGeometry

namespace OAI

namespace BinPackingGap
namespace UniformTree

def graftLeaves (T : UniformTree) (G : T.leaves → UniformTree) : Finset (List ℕ) :=
  Finset.univ.biUnion (fun l : T.leaves =>
    (G l).leaves.image (fun w => l.val ++ w))

theorem mem_graftLeaves (T : UniformTree) (G : T.leaves → UniformTree)
    {x : List ℕ} :
    x ∈ graftLeaves T G ↔ ∃ l : T.leaves, ∃ w ∈ (G l).leaves, x = l.val ++ w := by
  constructor
  · intro hx
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨w, hw, hx⟩ := Finset.mem_image.mp hl
    exact ⟨l, w, hw, hx.symm⟩
  · rintro ⟨l, w, hw, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩

def graft (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) : UniformTree where
  height := T.height + N
  leaves := graftLeaves T G
  leaves_nonempty := by
    obtain ⟨l, hl⟩ := T.leaves_nonempty
    obtain ⟨w, hw⟩ := (G ⟨l, hl⟩).leaves_nonempty
    exact ⟨l ++ w, (mem_graftLeaves T G).mpr ⟨⟨l, hl⟩, w, hw, rfl⟩⟩
  length_leaf := by
    intro x hx
    obtain ⟨l, w, hw, rfl⟩ := (mem_graftLeaves T G).mp hx
    rw [List.length_append, T.length_leaf l.val l.property,
      (G l).length_leaf w hw, hG l]
  positive_labels := by
    intro x hx a ha
    obtain ⟨l, w, hw, rfl⟩ := (mem_graftLeaves T G).mp hx
    rcases List.mem_append.mp ha with ha | ha
    · exact T.positive_labels l.val l.property a ha
    · exact (G l).positive_labels w hw a ha

@[simp] theorem graft_height (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) :
    (graft T G N hG).height = T.height + N := rfl

theorem mem_graft_leaves (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) {x : List ℕ} :
    x ∈ (graft T G N hG).leaves ↔
      ∃ l : T.leaves, ∃ w ∈ (G l).leaves, x = l.val ++ w :=
  mem_graftLeaves T G

theorem append_eq_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (u v : List ℕ) :
    l₁.val ++ u = l₂.val ++ v ↔ l₁ = l₂ ∧ u = v := by
  constructor
  · intro h
    have hlen : l₁.val.length = l₂.val.length :=
      (T.length_leaf l₁.val l₁.property).trans (T.length_leaf l₂.val l₂.property).symm
    exact ⟨Subtype.ext (List.append_inj_left h hlen), List.append_inj_right h hlen⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem old_prefix_iff (T : UniformTree) {u : List ℕ} (hu : u ∈ T.vertices)
    (l : T.leaves) (w : List ℕ) :
    u.IsPrefix (l.val ++ w) ↔ u.IsPrefix l.val := by
  apply List.isPrefix_append_of_length
  rw [T.length_leaf l.val l.property]
  exact T.length_le_height hu

theorem leaf_prefix_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (w : List ℕ) : l₁.val.IsPrefix (l₂.val ++ w) ↔ l₁ = l₂ := by
  rw [T.old_prefix_iff (T.leaf_mem_vertices l₁.property) l₂ w]
  constructor
  · intro h
    exact Subtype.ext (h.eq_of_length
      ((T.length_leaf l₁.val l₁.property).trans
        (T.length_leaf l₂.val l₂.property).symm))
  · rintro rfl
    exact List.prefix_refl l₁.val

theorem vertices_subset_graft (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) :
    T.vertices ⊆ (graft T G N hG).vertices := by
  intro u hu
  obtain ⟨l, hl, hul⟩ := T.mem_vertices_iff.mp hu
  let oldLeaf : T.leaves := ⟨l, hl⟩
  obtain ⟨w, hw⟩ := (G oldLeaf).leaves_nonempty
  apply (graft T G N hG).mem_vertices_iff.mpr
  refine ⟨l ++ w, ?_, hul.trans (List.prefix_append l w)⟩
  exact (mem_graft_leaves T G N hG).mpr ⟨oldLeaf, w, hw, rfl⟩

theorem append_mem_graft_vertices (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) (l : T.leaves)
    {v : List ℕ} (hv : v ∈ (G l).vertices) :
    l.val ++ v ∈ (graft T G N hG).vertices := by
  obtain ⟨w, hw, hvw⟩ := (G l).mem_vertices_iff.mp hv
  exact (graft T G N hG).mem_vertices_iff.mpr
    ⟨l.val ++ w, (mem_graft_leaves T G N hG).mpr ⟨l, w, hw, rfl⟩,
      (List.prefix_append_right_inj l.val).mpr hvw⟩

theorem mem_graft_vertices_iff (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) {x : List ℕ} :
    x ∈ (graft T G N hG).vertices ↔
      x ∈ T.vertices ∨
        ∃ l : T.leaves, ∃ v ∈ (G l).vertices, v ≠ [] ∧ x = l.val ++ v := by
  constructor
  · intro hx
    obtain ⟨word, hword, hp⟩ := (graft T G N hG).mem_vertices_iff.mp hx
    obtain ⟨l, w, hw, rfl⟩ := (mem_graft_leaves T G N hG).mp hword
    have hx' : x ∈ prefixes (l.val ++ w) := mem_prefixes_iff.mpr hp
    rw [prefixes_append_eq] at hx'
    rcases Finset.mem_union.mp hx' with h | h
    · exact Or.inl (T.mem_vertices_iff.mpr
        ⟨l.val, l.property, mem_prefixes_iff.mp h⟩)
    · obtain ⟨v, hv, hpv, heq⟩ := mem_prefixesAfter_iff.mp h
      exact Or.inr ⟨l, v, (G l).mem_vertices_iff.mpr ⟨w, hw, hpv⟩, hv, heq.symm⟩
  · rintro (hx | ⟨l, v, hv, _, rfl⟩)
    · exact vertices_subset_graft T G N hG hx
    · exact append_mem_graft_vertices T G N hG l hv

theorem append_not_mem_old_vertices (T : UniformTree) (l : T.leaves)
    {v : List ℕ} (hv : v ≠ []) : l.val ++ v ∉ T.vertices := by
  intro h
  have hlen := T.length_le_height h
  rw [List.length_append, T.length_leaf l.val l.property] at hlen
  have hz : v.length = 0 := by omega
  exact hv (List.length_eq_zero_iff.mp hz)

theorem filter_old_prefix_append (T : UniformTree) (marks : Finset (List ℕ))
    (hmarks : marks ⊆ T.vertices) (l : T.leaves) (w : List ℕ) :
    marks.filter (fun u => u.IsPrefix (l.val ++ w)) =
      marks.filter (fun u => u.IsPrefix l.val) := by
  apply Finset.filter_congr
  intro u hu
  exact T.old_prefix_iff (hmarks hu) l w

theorem append_not_prefix_of_ne_leaves (T : UniformTree) (l₁ l₂ : T.leaves)
    (hne : l₁ ≠ l₂) (u v : List ℕ) :
    ¬ (l₁.val ++ u).IsPrefix (l₂.val ++ v) := by
  intro h
  apply hne
  exact (T.leaf_prefix_append_iff l₁ l₂ v).mp
    ((List.prefix_append l₁.val u).trans h)

theorem append_prefix_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (u v : List ℕ) :
    (l₁.val ++ u).IsPrefix (l₂.val ++ v) ↔ l₁ = l₂ ∧ u.IsPrefix v := by
  constructor
  · intro h
    have heq : l₁ = l₂ := (T.leaf_prefix_append_iff l₁ l₂ v).mp
      ((List.prefix_append l₁.val u).trans h)
    subst l₂
    exact ⟨rfl, (List.prefix_append_right_inj l₁.val).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (List.prefix_append_right_inj l₁.val).mpr h

theorem filter_other_lift_prefix (T : UniformTree) (l₁ l₂ : T.leaves)
    (hne : l₁ ≠ l₂) (marks : Finset (List ℕ)) (w : List ℕ) :
    (marks.image (fun u => l₁.val ++ u)).filter
      (fun u => u.IsPrefix (l₂.val ++ w)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hx
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hm
  exact T.append_not_prefix_of_ne_leaves l₁ l₂ hne u w hp

theorem old_disjoint_lift (T : UniformTree) (old : Finset (List ℕ))
    (hold : old ⊆ T.vertices) (l : T.leaves) (marks : Finset (List ℕ))
    (hroot : [] ∉ marks) : Disjoint old (marks.image (fun u => l.val ++ u)) := by
  apply Finset.disjoint_left.mpr
  intro x hxold hxlift
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hxlift
  have hne : u ≠ [] := by
    intro heq
    exact hroot (heq ▸ hu)
  exact T.append_not_mem_old_vertices l hne (hold hxold)

end UniformTree
end BinPackingGap

end OAI
