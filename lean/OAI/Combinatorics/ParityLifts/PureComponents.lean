import OAI.Combinatorics.ParityLifts.ColorSpan

namespace OAI

namespace ParityWL

open scoped BigOperators

section InducedBagTree

open scoped Classical

variable {A N : Type} {R : A → A → Prop} {t : ℕ}

noncomputable def RankedBagTree.induce (D : RankedBagTree (N := N) R t) (P : A → Prop) :
    RankedBagTree (N := N) (fun a b : Subtype P => R a.1 b.1) t where
  toRankedTree := D.toRankedTree
  bag n := (D.bag n).subtype P
  top a := D.top a.1
  top_mem a := Finset.mem_subtype.mpr (D.top_mem a.1)
  top_ancestor a n ha := D.top_ancestor a.1 n (Finset.mem_subtype.mp ha)
  interval_mem a n l hn hnl ha :=
    Finset.mem_subtype.mpr (D.interval_mem a.1 n l hn hnl (Finset.mem_subtype.mp ha))
  edge_cover a b hab := by
    obtain ⟨n, han, hbn⟩ := D.edge_cover a.1 b.1 hab
    exact ⟨n, Finset.mem_subtype.mpr han, Finset.mem_subtype.mpr hbn⟩
  width n := by
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans (D.width n)
  intersection n hn := by
    let : DecidableEq (Subtype P) := Classical.decEq _
    have he : (D.bag n).subtype P ∩ (D.bag (D.parent n)).subtype P =
        (D.bag n ∩ D.bag (D.parent n)).subtype P := by
      ext a
      simp only [Finset.mem_inter, Finset.mem_subtype]
    rw [he, Finset.card_subtype]
    exact lt_of_le_of_lt (Finset.card_filter_le _ _) (D.intersection n hn)

end InducedBagTree

section PureComponents

open scoped Classical

variable {k t : ℕ} (F : RootedTest k t)
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def PureLeftMaps :=
  {f : RelationMaps F.relation (G.sum H) // ∀ i, (f.1 (F.roots i)).isLeft}

noncomputable instance pureLeftMapsFintype [Fintype V] [Fintype W] : Fintype (PureLeftMaps F G H) := by
  unfold PureLeftMaps
  infer_instance

def ComponentMask := {s : F.Vertex → Bool //
  (∀ a b, F.relation a b → s a = s b) ∧ ∀ i, s (F.roots i) = true}

noncomputable instance componentMaskFintype : Fintype (ComponentMask F) := by
  unfold ComponentMask
  infer_instance

abbrev MaskLeft (s : ComponentMask F) := {a : F.Vertex // s.1 a = true}
abbrev MaskRight (s : ComponentMask F) := {a : F.Vertex // s.1 a = false}

noncomputable def ComponentMaps (s : ComponentMask F) :=
  RelationMaps (fun a b : MaskLeft F s => F.relation a.1 b.1) G ×
  RelationMaps (fun a b : MaskRight F s => F.relation a.1 b.1) H

noncomputable instance componentMapsFintype [Fintype V] [Fintype W] (s : ComponentMask F) :
    Fintype (ComponentMaps F G H s) := by
  unfold ComponentMaps
  infer_instance

noncomputable def assembleFunction (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : F.Vertex) : V ⊕ W :=
  if h : s.1 a = true then .inl (f.1.1 ⟨a, h⟩)
  else .inr (f.2.1 ⟨a, Bool.eq_false_iff.mpr h⟩)

lemma assembleFunction_left (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : MaskLeft F s) : assembleFunction F G H s f a.1 = .inl (f.1.1 a) := by
  simp only [assembleFunction, dite_eq_left a.2]

lemma assembleFunction_right (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : MaskRight F s) : assembleFunction F G H s f a.1 = .inr (f.2.1 a) := by
  have ha : s.1 a.1 ≠ true := by rw [a.2]; decide
  simp only [assembleFunction, dite_eq_right ha]

lemma assembleFunction_isLeft (s : ComponentMask F) (f : ComponentMaps F G H s)
    (a : F.Vertex) : (assembleFunction F G H s f a).isLeft = s.1 a := by
  by_cases h : s.1 a = true
  · rw [assembleFunction_left F G H s f ⟨a, h⟩]
    exact h.symm
  · rw [assembleFunction_right F G H s f ⟨a, Bool.eq_false_iff.mpr h⟩]
    exact (Bool.eq_false_iff.mpr h).symm

noncomputable def assemblePure (f : (s : ComponentMask F) × ComponentMaps F G H s) :
    PureLeftMaps F G H := ⟨⟨assembleFunction F G H f.1 f.2, by
      intro a b hab
      have he := f.1.2.1 a b hab
      by_cases ha : f.1.1 a = true
      · have hb : f.1.1 b = true := he.symm.trans ha
        rw [assembleFunction_left F G H f.1 f.2 ⟨a, ha⟩,
          assembleFunction_left F G H f.1 f.2 ⟨b, hb⟩]
        exact f.2.1.2 ⟨a, ha⟩ ⟨b, hb⟩ hab
      · have ha' : f.1.1 a = false := Bool.eq_false_iff.mpr ha
        have hb : f.1.1 b = false := he.symm.trans ha'
        rw [assembleFunction_right F G H f.1 f.2 ⟨a, ha'⟩,
          assembleFunction_right F G H f.1 f.2 ⟨b, hb⟩]
        exact f.2.2.2 ⟨a, ha'⟩ ⟨b, hb⟩ hab⟩,
      fun i => by rw [assembleFunction_isLeft]; exact f.1.2.2 i⟩

lemma assemblePure_injective : Function.Injective (assemblePure F G H) := by
  rintro ⟨s, f⟩ ⟨s', f'⟩ he
  have hefun (a : F.Vertex) : assembleFunction F G H s f a = assembleFunction F G H s' f' a :=
    congrFun (congrArg (fun p => p.1.1) he) a
  have hs : s = s' := by
    apply Subtype.ext
    funext a
    rw [← assembleFunction_isLeft F G H s f a, ← assembleFunction_isLeft F G H s' f' a, hefun a]
  subst s'
  apply congrArg (Sigma.mk s)
  apply Prod.ext
  · apply Subtype.ext
    funext a
    apply Sum.inl_injective
    rw [← assembleFunction_left F G H s f a, ← assembleFunction_left F G H s f' a]
    exact hefun a.1
  · apply Subtype.ext
    funext a
    apply Sum.inr_injective
    rw [← assembleFunction_right F G H s f a, ← assembleFunction_right F G H s f' a]
    exact hefun a.1

lemma sum_adj_same_side {a b : V ⊕ W} (h : (G.sum H).Adj a b) : a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp_all only [SimpleGraph.sum_adj, Sum.isLeft_inl, Sum.isLeft_inr]

noncomputable def mapMask (f : PureLeftMaps F G H) : ComponentMask F :=
  ⟨fun a => (f.1.1 a).isLeft,
    (fun a b hab => sum_adj_same_side G H (f.1.2 a b hab)), f.2⟩

noncomputable def mapComponents (f : PureLeftMaps F G H) : ComponentMaps F G H (mapMask F G H f) :=
  (⟨fun a => (f.1.1 a.1).getLeft a.2, by
    intro a b hab
    have he := f.1.2 a.1 b.1 hab
    rw [← Sum.inl_getLeft (f.1.1 a.1) a.2, ← Sum.inl_getLeft (f.1.1 b.1) b.2] at he
    exact he⟩,
  ⟨fun a => (f.1.1 a.1).getRight (Sum.isLeft_eq_false.mp a.2), by
    intro a b hab
    have he := f.1.2 a.1 b.1 hab
    rw [← Sum.inr_getRight (f.1.1 a.1) (Sum.isLeft_eq_false.mp a.2),
      ← Sum.inr_getRight (f.1.1 b.1) (Sum.isLeft_eq_false.mp b.2)] at he
    exact he⟩)

lemma assemble_mapComponents (f : PureLeftMaps F G H) :
    assemblePure F G H ⟨mapMask F G H f, mapComponents F G H f⟩ = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext a
  change assembleFunction F G H (mapMask F G H f) (mapComponents F G H f) a = f.1.1 a
  by_cases h : (f.1.1 a).isLeft = true
  · rw [assembleFunction_left F G H (mapMask F G H f) (mapComponents F G H f) ⟨a, h⟩]
    exact Sum.inl_getLeft _ _
  · rw [assembleFunction_right F G H (mapMask F G H f) (mapComponents F G H f)
      ⟨a, Bool.eq_false_iff.mpr h⟩]
    exact Sum.inr_getRight _ _

noncomputable def componentEquiv :
    ((s : ComponentMask F) × ComponentMaps F G H s) ≃ PureLeftMaps F G H :=
  Equiv.ofBijective (assemblePure F G H) ⟨assemblePure_injective F G H,
    fun f => ⟨⟨mapMask F G H f, mapComponents F G H f⟩, assemble_mapComponents F G H f⟩⟩

lemma pureLeft_card [Fintype V] [Fintype W] :
    Fintype.card (PureLeftMaps F G H) =
      ∑ s : ComponentMask F,
        Fintype.card (RelationMaps (fun a b : MaskLeft F s => F.relation a.1 b.1) G) *
        Fintype.card (RelationMaps (fun a b : MaskRight F s => F.relation a.1 b.1) H) := by
  rw [← Fintype.card_congr (componentEquiv F G H), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact Fintype.card_prod _ _

end PureComponents

end ParityWL

end OAI
