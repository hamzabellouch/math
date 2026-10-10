import OAI.Combinatorics.GraphThreshold.ProbabilityTreeFacts

namespace OAI

/-! Full-path interpretation of supports and structural disjointness. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai.ProbabilityTree

variable {X : Type} [DecidableEq X]

theorem pathUnion_subset_support {d : ℕ} (T : ProbabilityTree X d) (p : T.Path) :
    T.pathUnion p ⊆ T.support := by
  induction T with
  | leaf => exact Finset.empty_subset _
  | @node d B inst law positive label child ih =>
      rcases p with ⟨b, p⟩
      exact Finset.union_subset (label_subset_support law positive label child b)
        ((ih b p).trans (child_support_subset law positive label child b))

theorem mem_pathUnion_iff {d : ℕ} (T : ProbabilityTree X d) (p : T.Path) (x : X) :
    x ∈ T.pathUnion p ↔ ∃ S ∈ T.pathLabels p, x ∈ S := by
  induction T with
  | leaf => simp [pathUnion, pathLabels]
  | @node d B inst law positive label child ih =>
      rcases p with ⟨b, p⟩
      simp [pathUnion, pathLabels, ih b p]

theorem pathLabel_subset_pathUnion {d : ℕ} (T : ProbabilityTree X d)
    (p : T.Path) {S : Finset X} (hS : S ∈ T.pathLabels p) : S ⊆ T.pathUnion p := by
  intro x hx
  exact (mem_pathUnion_iff T p x).2 ⟨S, hS, hx⟩

theorem pathLabel_subset_support {d : ℕ} (T : ProbabilityTree X d)
    (p : T.Path) {S : Finset X} (hS : S ∈ T.pathLabels p) : S ⊆ T.support :=
  (pathLabel_subset_pathUnion T p hS).trans (pathUnion_subset_support T p)

/-- Every arc coordinate occurs on an actual full path, since all branches continue. -/
theorem mem_support_iff_exists_path {d : ℕ} (T : ProbabilityTree X d) (x : X) :
    x ∈ T.support ↔ ∃ p : T.Path, x ∈ T.pathUnion p := by
  induction T with
  | leaf => simp [support, pathUnion]
  | @node d B inst law positive label child ih =>
      constructor
      · intro hx
        obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.mp hx
        rcases Finset.mem_union.mp hxb with hlabel | hchild
        · exact ⟨⟨b, choosePath (child b)⟩, Finset.mem_union_left _ hlabel⟩
        · obtain ⟨p, hp⟩ := (ih b).1 hchild
          exact ⟨⟨b, p⟩, Finset.mem_union_right _ hp⟩
      · rintro ⟨⟨b, p⟩, hx⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨b, Finset.mem_univ _, ?_⟩
        rcases Finset.mem_union.mp hx with hlabel | hchild
        · exact Finset.mem_union_left _ hlabel
        · exact Finset.mem_union_right _ ((ih b).2 ⟨p, hchild⟩)

theorem support_eq_pathUnion_biUnion {d : ℕ} (T : ProbabilityTree X d) :
    T.support = Finset.univ.biUnion T.pathUnion := by
  ext x
  simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and] using
    mem_support_iff_exists_path T x

theorem isDisjoint_iff_pathDisjoint {d : ℕ} (T : ProbabilityTree X d) :
    T.IsDisjoint ↔ T.PathDisjoint := by
  induction T with
  | leaf => simp [IsDisjoint, PathDisjoint, pathLabels]
  | @node d B inst law positive label child ih =>
      constructor
      · intro hT p
        rcases p with ⟨b, p⟩
        apply List.pairwise_cons.mpr
        constructor
        · intro S hS
          exact (hT.1 b).mono_right (pathLabel_subset_support (child b) p hS)
        · exact (ih b).1 (hT.2 b) p
      · intro hT
        constructor
        · intro b
          apply Finset.disjoint_left.mpr
          intro x hxLabel hxSupport
          obtain ⟨p, hp⟩ := (mem_support_iff_exists_path (child b) x).1 hxSupport
          obtain ⟨S, hS, hxS⟩ := (mem_pathUnion_iff (child b) p x).1 hp
          have hpw := hT ⟨b, p⟩
          have hdis := (List.pairwise_cons.mp hpw).1 S hS
          exact Finset.disjoint_left.mp hdis hxLabel hxS
        · intro b
          apply (ih b).2
          intro p
          exact (List.pairwise_cons.mp (hT ⟨b, p⟩)).2

theorem incoming_disjoint_subtree_of_pathDisjoint {d : ℕ} {B : Type} [Fintype B]
    {law : FiniteLaw B} {positive : law.IsPositive} {label : B → Finset X}
    {child : B → ProbabilityTree X d}
    (hT : (node B law positive label child).PathDisjoint) (b : B) :
    Disjoint (label b) (child b).support :=
  ((isDisjoint_iff_pathDisjoint _).2 hT).1 b

/-- The locality assertion applies even when disjointness is given in the literal path form. -/
theorem child_dependsOutside_of_pathDisjoint {d : ℕ} {B : Type} [Fintype B]
    {law : FiniteLaw B} {positive : law.IsPositive} {label : B → Finset X}
    {child : B → ProbabilityTree X d}
    (hT : (node B law positive label child).PathDisjoint) (b : B)
    {β : Type*} {f : Finset X → β} (hf : DependsOnlyOn (child b).support f) :
    DependsOutside (label b) f :=
  hf.dependsOutside (incoming_disjoint_subtree_of_pathDisjoint hT b)

theorem coveredBy_mono {d : ℕ} {T : ProbabilityTree X d} {W V : Finset X}
    (h : T.CoveredBy W) (hWV : W ⊆ V) : T.CoveredBy V := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hWV⟩

theorem coveredBy_univ [Fintype X] {d : ℕ} (T : ProbabilityTree X d) :
    T.CoveredBy Finset.univ :=
  ⟨choosePath T, Finset.subset_univ _⟩

end LeanBlast.SecondKahnKalai.ProbabilityTree

end

end OAI
