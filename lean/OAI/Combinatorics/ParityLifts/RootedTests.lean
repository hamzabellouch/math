import OAI.Combinatorics.ParityLifts.RankedTrees

namespace OAI

namespace ParityWL

open scoped BigOperators

section RootedTests

open scoped Classical

/-- Sources may have loops during root gluing. A loop contributes zero on every
simple target; it is never silently deleted. -/
structure RootedTest (k t : ℕ) where
  Vertex : Type
  vertexFintype : Fintype Vertex
  relation : Vertex → Vertex → Prop
  symmetric : Std.Symm relation
  roots : Fin k → Vertex
  Node : Type
  nodeFintype : Fintype Node
  tree : RankedBagTree (N := Node) relation t
  root_bag : tree.bag tree.root = Finset.univ.image roots

attribute [instance] RootedTest.vertexFintype RootedTest.nodeFintype

noncomputable def RelationMaps {A V : Type} (R : A → A → Prop) (G : SimpleGraph V) :=
  {f : A → V // ∀ a b, R a b → G.Adj (f a) (f b)}

noncomputable instance relationMapsFintype {A V : Type} [Fintype A] [Fintype V]
    (R : A → A → Prop) (G : SimpleGraph V) : Fintype (RelationMaps R G) := by
  unfold RelationMaps
  infer_instance

noncomputable def RootedTest.Maps {k t : ℕ} (F : RootedTest k t) {V : Type}
    (G : SimpleGraph V) (x : Fin k → V) :=
  {f : RelationMaps F.relation G // ∀ i, f.1 (F.roots i) = x i}

noncomputable instance rootedMapsFintype {k t : ℕ} (F : RootedTest k t)
    {V : Type} [Fintype V] (G : SimpleGraph V) (x : Fin k → V) : Fintype (F.Maps G x) := by
  unfold RootedTest.Maps
  infer_instance

noncomputable def RootedTest.count {k t : ℕ} (F : RootedTest k t)
    {V : Type} [Fintype V] (G : SimpleGraph V) (x : Fin k → V) : ℚ :=
  Fintype.card (F.Maps G x)

noncomputable def RootedTest.totalEquiv {k t : ℕ} (F : RootedTest k t)
    {V : Type} (G : SimpleGraph V) :
    ((x : Fin k → V) × F.Maps G x) ≃ RelationMaps F.relation G where
  toFun f := f.2.1
  invFun f := ⟨fun i => f.1 (F.roots i), ⟨f, fun _ => rfl⟩⟩
  left_inv f := by
    rcases f with ⟨x, f, hf⟩
    have he : (fun i => f.1 (F.roots i)) = x := funext hf
    subst x
    rfl
  right_inv _ := rfl

lemma RootedTest.sum_count {k t : ℕ} (F : RootedTest k t)
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∑ x : Fin k → V, F.count G x = (Fintype.card (RelationMaps F.relation G) : ℚ) := by
  unfold count
  rw [← Nat.cast_sum, ← Fintype.card_sigma, Fintype.card_congr (F.totalEquiv G)]

noncomputable def relationMapsSimpleEquiv {A V : Type} (F : SimpleGraph A)
    (G : SimpleGraph V) : RelationMaps F.Adj G ≃ (F →g G) where
  toFun f := ⟨f.1, fun h => f.2 _ _ h⟩
  invFun f := ⟨f, fun _ _ h => f.map_adj h⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma relationMaps_loop {A V : Type} [Fintype A] [Fintype V]
    (R : A → A → Prop) (G : SimpleGraph V) {a : A} (ha : R a a) :
    Fintype.card (RelationMaps R G) = 0 := by
  have : IsEmpty (RelationMaps R G) := ⟨fun f => (f.2 a a ha).ne rfl⟩
  exact Fintype.card_eq_zero

lemma no_choice_equal_relation {W N : Type} [Fintype W] [Fintype N]
    {t : ℕ} (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful)
    (R : W → W → Prop) (hs : Std.Symm R) (D : RankedBagTree (N := N) R t) :
    Fintype.card (RelationMaps R (zeroLift C)) = Fintype.card (RelationMaps R (starLift C)) := by
  by_cases hloop : ∃ x, R x x
  · obtain ⟨x, hx⟩ := hloop
    rw [relationMaps_loop R _ hx, relationMaps_loop R _ hx]
  · let F : SimpleGraph W := ⟨R, hs, ⟨fun x hx => hloop ⟨x, hx⟩⟩⟩
    have hz : Fintype.card (RelationMaps R (zeroLift C)) = homCount F (zeroLift C) :=
      (homCount_card_equiv (zeroLift C) F (relationMapsSimpleEquiv F (zeroLift C)).symm).symm
    have ho : Fintype.card (RelationMaps R (starLift C)) = homCount F (starLift C) :=
      (homCount_card_equiv (starLift C) F (relationMapsSimpleEquiv F (starLift C)).symm).symm
    rw [hz, ho]
    exact no_choice_equal_decomposed C ht hn F D

lemma no_choice_equal_rooted_total {k t : ℕ} (F : RootedTest k t)
    (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful) :
    ∑ x, F.count (zeroLift C) x = ∑ x, F.count (starLift C) x := by
  rw [F.sum_count, F.sum_count,
    no_choice_equal_relation C ht hn F.relation F.symmetric F.tree]

noncomputable def singleBagTest {k t : ℕ} {A : Type} [Fintype A]
    (R : A → A → Prop) (hs : Std.Symm R) (r : Fin k → A)
    (hr : Function.Surjective r) (hA : Fintype.card A ≤ t) : RootedTest k t where
  Vertex := A
  vertexFintype := inferInstance
  relation := R
  symmetric := hs
  roots := r
  Node := Unit
  nodeFintype := inferInstance
  tree :=
    { root := ()
      parent := fun _ => ()
      rank := fun _ => 0
      parent_lt := by intro i hi; exact (hi (Subsingleton.elim _ _)).elim
      bag := fun _ => Finset.univ
      top := fun _ => ()
      top_mem := fun _ => Finset.mem_univ _
      top_ancestor := by intro x i _; cases i; exact .refl
      interval_mem := by intros; exact Finset.mem_univ _
      edge_cover := fun _ _ _ => ⟨(), Finset.mem_univ _, Finset.mem_univ _⟩
      width := by intro _; simpa only [Finset.card_univ] using hA
      intersection := by intro i hi; exact (hi (Subsingleton.elim _ _)).elim }
  root_bag := by
    ext a
    simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff]
    exact hr a

noncomputable def isolatedTest (k t : ℕ) (hkt : k ≤ t) : RootedTest k t :=
  singleBagTest (fun _ _ : Fin k => False) ⟨fun _ _ h => h⟩ id Function.surjective_id
    (by simpa using hkt)

lemma isolatedTest_count (k t : ℕ) (hkt : k ≤ t) {V : Type} [Fintype V]
    (G : SimpleGraph V) (x : Fin k → V) : (isolatedTest k t hkt).count G x = 1 := by
  let f : (isolatedTest k t hkt).Maps G x := ⟨⟨x, fun _ _ h => h.elim⟩, fun _ => rfl⟩
  have hi : Unique ((isolatedTest k t hkt).Maps G x) :=
    { default := f
      uniq := by
        intro g
        apply Subtype.ext
        apply Subtype.ext
        funext i
        exact g.2 i }
  simp only [RootedTest.count, Fintype.card_unique, Nat.cast_one]

end RootedTests

end ParityWL

end OAI
