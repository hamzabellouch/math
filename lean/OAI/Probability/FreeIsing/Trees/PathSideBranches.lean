import OAI.Probability.FreeIsing.Trees.ConeCoding

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

def cone {d : ℕ} (r : TreeVertex d) : Set (TreeVertex d) :=
  {v | r.1 <+: v.1}

def sideColor {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : Fin d :=
  Classical.choose (Fin.exists_ne_and_ne_of_two_lt v.1[i]
    (v.1.getD (i.1 + 1) v.1[i]) (by omega))

theorem sideColor_ne_incoming {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : sideColor hd v i ≠ v.1[i] :=
  (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt v.1[i]
    (v.1.getD (i.1 + 1) v.1[i]) (by omega))).1

theorem sideColor_ne_outgoing {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) (hi : i.1 + 1 < v.1.length) :
    sideColor hd v i ≠ v.1[i.1 + 1] := by
  have h := (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt v.1[i]
    (v.1.getD (i.1 + 1) v.1[i]) (by omega))).2
  change sideColor hd v i ≠ v.1.getD (i.1 + 1) v.1[i] at h
  rw [List.getD_eq_getElem _ _ hi] at h
  exact h

private theorem take_target_ne_nil {d : ℕ} (v : TreeVertex d)
    (i : Fin v.1.length) : v.1.take (i.1 + 1) ≠ [] := by
  have hlen : (v.1.take (i.1 + 1)).length = i.1 + 1 := by
    simp only [List.length_take, Nat.min_eq_left (by omega : i.1 + 1 ≤ v.1.length)]
  intro h
  rw [h] at hlen
  simp at hlen

def sideVertex {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : TreeVertex d :=
  ⟨v.1.take (i.1 + 1) ++ [sideColor hd v i], by
    apply (TreeConeCoding.chain_append_iff _ _ _ (take_target_ne_nil v i)).mpr
    refine ⟨v.2.take _, ?_⟩
    simp only [List.take_succ_eq_append_getElem i.2, List.getLast_append_singleton]
    exact List.isChain_cons_cons.mpr
      ⟨(sideColor_ne_incoming hd v i).symm, List.IsChain.singleton _⟩⟩

@[simp] theorem sideVertex_val {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) :
    (sideVertex hd v i).1 = v.1.take (i.1 + 1) ++ [sideColor hd v i] := rfl

@[simp] theorem sideVertex_length {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : (sideVertex hd v i).1.length = i.1 + 2 := by
  simp only [sideVertex_val, List.length_append, List.length_take,
    Nat.min_eq_left (by omega : i.1 + 1 ≤ v.1.length), List.length_singleton]

@[simp] theorem parent_sideVertex {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) :
    parentVertex (sideVertex hd v i) = ConnectedHull.takeVertex v (i.1 + 1) := by
  apply Subtype.ext
  simp [parentVertex, sideVertex, ConnectedHull.takeVertex]

theorem sideVertex_adj {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) :
    treeAdj (ConnectedHull.takeVertex v (i.1 + 1)) (sideVertex hd v i) :=
  Or.inl ⟨sideColor hd v i, rfl⟩

private theorem not_prefix_wrong_color {α : Type*} (w : List α) {n : ℕ}
    (hn : n < w.length) {c : α} (hc : c ≠ w[n]) :
    ¬ w.take n ++ [c] <+: w := by
  intro h
  have hlen : (w.take n).length = n := by
    simp only [List.length_take, Nat.min_eq_left hn.le]
  have hidx : n < (w.take n ++ [c]).length := by
    simp only [List.length_append, hlen, List.length_singleton]
    omega
  have he := h.getElem hidx
  have hread : (w.take n ++ [c])[n] = c := by
    simpa only [hlen, Nat.sub_self, List.getElem_cons_zero] using
      (List.getElem_append_right (as := w.take n) (bs := [c])
        (i := n) (h₂ := hidx) (by omega))
  exact hc (hread.symm.trans he)

theorem sideVertex_not_prefix {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : ¬ (sideVertex hd v i).1 <+: v.1 := by
  by_cases hi : i.1 + 1 < v.1.length
  · exact not_prefix_wrong_color v.1 hi (sideColor_ne_outgoing hd v i hi)
  · intro h
    have := h.length_le
    rw [sideVertex_length] at this
    omega

theorem cone_mono {d : ℕ} {r s : TreeVertex d} (h : r.1 <+: s.1) :
    cone s ⊆ cone r := fun _ hu => h.trans hu

theorem path_vertex_not_mem_sideCone {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) (k : ℕ) :
    ConnectedHull.takeVertex v k ∉ cone (sideVertex hd v i) := by
  intro h
  exact sideVertex_not_prefix hd v i (h.trans (List.take_prefix k v.1))

theorem sideCone_disjoint_later_forward {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j) :
    Disjoint (cone (sideVertex hd v i))
      (cone (ConnectedHull.takeVertex v (j.1 + 1))) := by
  apply Set.disjoint_left.mpr
  intro u hu hv
  have hlen : (sideVertex hd v i).1.length ≤
      (ConnectedHull.takeVertex v (j.1 + 1)).1.length := by
    rw [sideVertex_length]
    change i.1 + 2 ≤ (v.1.take (j.1 + 1)).length
    rw [List.length_take, Nat.min_eq_left (by omega : j.1 + 1 ≤ v.1.length)]
    exact Nat.succ_le_succ (Fin.lt_def.mp hij)
  have hp := List.prefix_of_prefix_length_le hu hv hlen
  exact sideVertex_not_prefix hd v i (hp.trans (List.take_prefix _ _))

theorem sideCone_subset_forward {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : cone (sideVertex hd v i) ⊆
      cone (ConnectedHull.takeVertex v (i.1 + 1)) :=
  cone_mono (List.prefix_append _ _)

theorem sideCones_pairwise_disjoint {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d) :
    Pairwise (fun i j : Fin v.1.length =>
      Disjoint (cone (sideVertex hd v i)) (cone (sideVertex hd v j))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (sideCone_disjoint_later_forward hd v hlt).mono_right
      (sideCone_subset_forward hd v j)
  · exact ((sideCone_disjoint_later_forward hd v hgt).mono_right
      (sideCone_subset_forward hd v i)).symm

theorem cone_infinite {d : ℕ} (hd : 2 ≤ d) (r : TreeVertex d) (hr : r.1 ≠ []) :
    (cone r).Infinite := by
  cases d with
  | zero => omega
  | succ b =>
      have : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
      apply Set.infinite_coe_iff.mp
      change Infinite {v : TreeVertex (b + 1) // r.1 <+: v.1}
      exact (TreeConeCoding.coneEquiv r hr).infinite_iff.mp inferInstance

theorem sideCone_infinite {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : (cone (sideVertex hd v i)).Infinite := by
  apply cone_infinite (by omega)
  intro h
  have hl := sideVertex_length hd v i
  rw [h] at hl
  simp at hl

theorem edge_leaving_cone {d : ℕ} {r u w : TreeVertex d}
    (hu : u ∈ cone r) (hw : w ∉ cone r) (huw : treeAdj u w) :
    u = r ∧ w = parentVertex r := by
  have hur : u = r := by
    by_contra hne
    exact hw (treeAdj_preserves_prefix hu huw hne)
  subst u
  refine ⟨rfl, ?_⟩
  rcases huw with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact False.elim (hw (by
      change r.1 <+: w.1
      rw [hc]
      exact List.prefix_append _ _))
  · apply Subtype.ext
    change w.1 = r.1.dropLast
    rw [hc]
    simp

theorem sideCone_boundary {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) {u w : TreeVertex d}
    (hu : u ∈ cone (sideVertex hd v i)) (hw : w ∉ cone (sideVertex hd v i))
    (huw : treeAdj u w) :
    u = sideVertex hd v i ∧ w = ConnectedHull.takeVertex v (i.1 + 1) := by
  obtain ⟨hur, hwr⟩ := edge_leaving_cone hu hw huw
  exact ⟨hur, hwr.trans (parent_sideVertex hd v i)⟩

theorem reachable_in_cone {d : ℕ} {r u : TreeVertex d} (hu : u ∈ cone r) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
  have aux : ∀ n : ℕ, ∀ u : TreeVertex d, u.1.length = n → u ∈ cone r →
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hlen hu
      by_cases hur : u = r
      · subst u
        exact .refl
      · have hlt : r.1.length < u.1.length := by
          have hle := hu.length_le
          have hne : r.1.length ≠ u.1.length := by
            intro heq
            exact hur (Subtype.ext (hu.eq_of_length heq).symm)
          omega
        have hnil : u.1 ≠ [] := by
          intro h
          simp [h] at hlt
        have hp : parentVertex u ∈ cone r := by
          apply List.prefix_of_prefix_length_le hu (List.dropLast_prefix u.1)
          rw [List.length_dropLast]
          omega
        have hplen : (parentVertex u).1.length < n := by
          rw [parentVertex_length]
          omega
        exact (ih _ hplen _ rfl hp).tail ⟨hp, hu, treeAdj_parentVertex hnil⟩
  exact aux _ u rfl hu

theorem parent_not_mem_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    parentVertex r ∉ cone r := by
  intro h
  have hlen := h.length_le
  rw [parentVertex_length] at hlen
  have hpos := List.length_pos_iff.mpr hr
  omega

theorem mem_cone_iff_reachable_avoiding_parent {d : ℕ} (r u : TreeVertex d)
    (hr : r.1 ≠ []) : u ∈ cone r ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ parentVertex r ∧ y ≠ parentVertex r ∧ treeAdj x y)
      r u := by
  constructor
  · intro hu
    apply Relation.ReflTransGen.mono (fun x y hxy => ?_) r u (reachable_in_cone hu)
    exact ⟨fun h => parent_not_mem_cone r hr (h ▸ hxy.1),
      fun h => parent_not_mem_cone r hr (h ▸ hxy.2.1), hxy.2.2⟩
  · intro h
    induction h with
    | refl => exact List.prefix_refl _
    | tail h hxy ih =>
        by_contra hy
        exact hxy.2.1 (edge_leaving_cone ih hy hxy.2.2).2

end Problem367.PathSideBranches

end

end OAI
