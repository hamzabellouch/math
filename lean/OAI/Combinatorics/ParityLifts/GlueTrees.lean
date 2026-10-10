import OAI.Combinatorics.ParityLifts.RootedTests

namespace OAI

namespace ParityWL

open scoped BigOperators

section GlueTrees

open scoped Classical

variable {I : Type} {r : I → ℕ} {t : ℕ} (F : (i : I) → RootedTest (r i) t)

abbrev GlueNode := Option ((i : I) × {n : (F i).Node // n ≠ (F i).tree.root})

noncomputable def glueNodeMap (i : I) (n : (F i).Node) : GlueNode F :=
  if h : n = (F i).tree.root then none else some ⟨i, ⟨n, h⟩⟩

noncomputable def glueNodeParent : GlueNode F → GlueNode F
  | none => none
  | some ⟨i, n⟩ => glueNodeMap F i ((F i).tree.parent n)

noncomputable def glueNodeRank : GlueNode F → ℕ
  | none => 0
  | some ⟨i, n⟩ => (F i).tree.rank n + 1

noncomputable def glueTree : RankedTree (GlueNode F) where
  root := none
  parent := glueNodeParent F
  rank := glueNodeRank F
  parent_lt := by
    intro n hn
    cases n with
    | none => exact (hn rfl).elim
    | some q =>
      rcases q with ⟨i, n⟩
      simp only [glueNodeParent, glueNodeMap]
      split_ifs
      · simp only [glueNodeRank]; omega
      · simpa only [glueNodeRank, Nat.add_lt_add_iff_right] using
          (F i).tree.parent_lt n.1 n.2

lemma glueNodeMap_root (i : I) : glueNodeMap F i (F i).tree.root = none := by
  simp [glueNodeMap]

lemma glueNodeMap_nonroot (i : I) (n : (F i).Node) (hn : n ≠ (F i).tree.root) :
    glueNodeMap F i n = some ⟨i, ⟨n, hn⟩⟩ := by
  simp only [glueNodeMap, dite_eq_right hn]

lemma glueTree_map_ancestor (i : I) {a b : (F i).Node}
    (h : (F i).tree.toRankedTree.Ancestor a b) :
    (glueTree F).Ancestor (glueNodeMap F i a) (glueNodeMap F i b) := by
  apply RankedTree.Ancestor.map _ (glueTree F) (glueNodeMap F i) _ h
  intro j hj
  rw [glueNodeMap_nonroot F i j hj]
  apply RankedTree.Ancestor.step (by simp [glueTree])
  exact .refl

lemma glueTree_ancestor_from_some {i : I}
    {a : {n : (F i).Node // n ≠ (F i).tree.root}} {n : GlueNode F}
    (h : (glueTree F).Ancestor (some ⟨i, a⟩) n) :
    ∃ b : {n : (F i).Node // n ≠ (F i).tree.root}, n = some ⟨i, b⟩ ∧
      (F i).tree.toRankedTree.Ancestor a.1 b.1 := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | @step n hn h ih =>
    cases n with
    | none => exact (hn rfl).elim
    | some q =>
      rcases q with ⟨j, b⟩
      obtain ⟨c, hc, hac⟩ := ih
      change glueNodeMap F j ((F j).tree.parent b.1) = some ⟨i, c⟩ at hc
      by_cases hp : (F j).tree.parent b.1 = (F j).tree.root
      · simp only [glueNodeMap, dite_eq_left hp] at hc
        cases hc
      · rw [glueNodeMap_nonroot F j _ hp] at hc
        have hji : j = i := congrArg Sigma.fst (Option.some.inj hc)
        subst j
        have hb : (F i).tree.parent b.1 = c.1 := by
          have he : (⟨(F i).tree.parent b.1, hp⟩ : {n // n ≠ (F i).tree.root}) = c := by
            simpa only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hc
          exact congrArg Subtype.val he
        exact ⟨b, rfl, .step b.2 (by rwa [hb])⟩

lemma glueTree_ancestor_nonroot {i : I}
    {a b : {n : (F i).Node // n ≠ (F i).tree.root}}
    (h : (glueTree F).Ancestor (some ⟨i, a⟩) (some ⟨i, b⟩)) :
    (F i).tree.toRankedTree.Ancestor a.1 b.1 := by
  obtain ⟨c, hc, hac⟩ := glueTree_ancestor_from_some F h
  have he : b = c := by
    simpa only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hc
  rwa [he]

lemma RankedTree.ancestor_root_eq {N : Type} (D : RankedTree N) {i : N}
    (h : D.Ancestor i D.root) : i = D.root := by
  rcases h.cases' D with he | ⟨hne, _⟩
  · exact he
  · exact (hne rfl).elim

lemma rooted_top_eq_root (i : I) {a : (F i).Vertex}
    (ha : ∃ j, (F i).roots j = a) : (F i).tree.top a = (F i).tree.root := by
  apply RankedTree.ancestor_root_eq
  apply (F i).tree.top_ancestor
  rw [(F i).root_bag]
  simpa only [Finset.mem_image, Finset.mem_univ, true_and] using ha

lemma rooted_mem_ancestor (i : I) {a : (F i).Vertex} {n m : (F i).Node}
    (ha : ∃ j, (F i).roots j = a) (hn : (F i).tree.toRankedTree.Ancestor n m)
    (ham : a ∈ (F i).tree.bag m) : a ∈ (F i).tree.bag n := by
  apply (F i).tree.interval_mem a n m _ hn ham
  rw [rooted_top_eq_root F i ha]
  exact (F i).tree.toRankedTree.root_ancestor n

end GlueTrees

end ParityWL

end OAI
