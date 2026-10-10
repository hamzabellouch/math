import OAI.Combinatorics.ParityLifts.ChoiceExtraction

namespace OAI

namespace ParityWL

open scoped BigOperators

section DecompositionCuts

open scoped Classical

/-- A finite rooted tree is indexed in parent-before-child order. The cuts below
are the vertex sides of its edges. Validity is recorded separately. -/
structure RootedCuts (W : Type) where
  nodes : ℕ
  root : Fin nodes
  parent : Fin nodes → Fin nodes
  parent_lt : ∀ i, i ≠ root → parent i < i
  bag : Fin nodes → Finset W
  side : Fin nodes → Finset W

variable {W : Type} [Fintype W]

noncomputable def RootedCuts.separator (D : RootedCuts W) (i : Fin D.nodes) : Finset W :=
  D.bag i ∩ D.bag (D.parent i)

noncomputable def RootedCuts.reverseSide (D : RootedCuts W) (i : Fin D.nodes) : Finset W :=
  Finset.univ \ (D.separator i ∪ D.side i)

/-- At node `i`, region `i` is the parent branch; a child is indexed by itself.
All other regions are empty. -/
noncomputable def RootedCuts.branch (D : RootedCuts W) (i j : Fin D.nodes) : Finset W :=
  if j = i then (if i = D.root then ∅ else D.reverseSide i)
  else if j ≠ D.root ∧ D.parent j = i then D.side j else ∅

noncomputable def RootedCuts.branchSeparator (D : RootedCuts W)
    (i j : Fin D.nodes) : Finset W :=
  if j = i then (if i = D.root then ∅ else D.separator i)
  else if j ≠ D.root ∧ D.parent j = i then D.separator j else ∅

/-- Standard finite tree-decomposition cuts: the incident outer sides and the
bag partition the graph, and each cut is separated by the intersection of the
incident bags. The strict intersection bound is the reduced form. No parity
or graph-homomorphism property is part of this definition. -/
structure ReducedCutDecomposition (F : SimpleGraph W) (t : ℕ) extends RootedCuts W where
  width : ∀ i, (bag i).card ≤ t
  intersection : ∀ i, i ≠ root → (toRootedCuts.separator i).card < t
  side_disjoint : ∀ i, i ≠ root → Disjoint (side i) (toRootedCuts.separator i)
  boundary : ∀ i, i ≠ root → ∀ x ∈ side i, ∀ y,
    F.Adj x y → y ∉ side i → y ∈ toRootedCuts.separator i
  bag_disjoint : ∀ i j, Disjoint (bag i) (toRootedCuts.branch i j)
  branch_disjoint : ∀ i j k, j ≠ k →
    Disjoint (toRootedCuts.branch i j) (toRootedCuts.branch i k)
  vertex_cover : ∀ i x, x ∈ bag i ∨ ∃ j, x ∈ toRootedCuts.branch i j

variable {F : SimpleGraph W} {t : ℕ}

lemma ReducedCutDecomposition.reverse_boundary (D : ReducedCutDecomposition F t)
    (i : Fin D.nodes) (hi : i ≠ D.root) :
    ∀ x ∈ D.reverseSide i, ∀ y, F.Adj x y → y ∉ D.reverseSide i →
      y ∈ D.separator i := by
  intro x hx y he hy
  have hx' : x ∉ D.separator i ∧ x ∉ D.side i := by
    simpa [RootedCuts.reverseSide] using hx
  have hy' : y ∈ D.separator i ∨ y ∈ D.side i := by
    by_cases hs : y ∈ D.separator i
    · exact Or.inl hs
    · exact Or.inr (by simpa [RootedCuts.reverseSide, hs] using hy)
  rcases hy' with hy' | hy'
  · exact hy'
  · exact (hx'.1 (D.boundary i hi y hy' x he.symm hx'.2)).elim

lemma ReducedCutDecomposition.branchSeparator_sub (D : ReducedCutDecomposition F t)
    (i j : Fin D.nodes) : D.branchSeparator i j ⊆ D.bag i := by
  unfold RootedCuts.branchSeparator
  split_ifs with h hroot hp
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left
  · rw [← hp.2]
    exact Finset.inter_subset_right
  · exact Finset.empty_subset _

lemma ReducedCutDecomposition.branchSeparator_small (D : ReducedCutDecomposition F t)
    (ht : 0 < t) (i j : Fin D.nodes) : (D.branchSeparator i j).card < t := by
  unfold RootedCuts.branchSeparator
  split_ifs with h hroot hp
  · simpa using ht
  · exact D.intersection i hroot
  · exact D.intersection j hp.1
  · simpa using ht

lemma ReducedCutDecomposition.branch_boundary (D : ReducedCutDecomposition F t)
    (i j : Fin D.nodes) : ∀ x ∈ D.branch i j, ∀ y,
      F.Adj x y → y ∉ D.branch i j → y ∈ D.branchSeparator i j := by
  unfold RootedCuts.branch RootedCuts.branchSeparator
  split_ifs with h hroot hp
  · simp
  · exact D.reverse_boundary i hroot
  · exact D.boundary j hp.1
  · simp

noncomputable def ReducedCutDecomposition.region (D : ReducedCutDecomposition F t)
    (i : Fin D.nodes) (x : W) : Option (Fin D.nodes) :=
  if h : x ∈ D.bag i then none else
    some (Classical.choose ((D.vertex_cover i x).resolve_left h))

lemma ReducedCutDecomposition.region_none (D : ReducedCutDecomposition F t)
    (i : Fin D.nodes) : regionSet (D.region i) none = D.bag i := by
  ext x
  simp [regionSet, ReducedCutDecomposition.region]

lemma ReducedCutDecomposition.region_some (D : ReducedCutDecomposition F t)
    (i j : Fin D.nodes) : regionSet (D.region i) (some j) = D.branch i j := by
  ext x
  simp only [regionSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold ReducedCutDecomposition.region
  by_cases hx : x ∈ D.bag i
  · have hn : x ∉ D.branch i j := fun h => Finset.disjoint_left.mp
      (D.bag_disjoint i j) hx h
    simp [hx, hn]
  · rw [dite_eq_right hx, Option.some.injEq]
    let k := Classical.choose ((D.vertex_cover i x).resolve_left hx)
    have hk : x ∈ D.branch i k := Classical.choose_spec
      ((D.vertex_cover i x).resolve_left hx)
    constructor
    · intro he
      exact he ▸ hk
    · intro hj
      by_contra hn
      exact (Finset.disjoint_left.mp (D.branch_disjoint i k j hn)) hk hj

variable {a : F →g template t}

lemma ReducedCutDecomposition.main_side_equal (D : ReducedCutDecomposition F t)
    (w : WeightedWitness (template t) F a (starParity t))
    (i : Fin D.nodes) (hi : i ≠ D.root) (j k : Fin t)
    (hj : ∀ x ∈ D.separator i, a x ≠ .inl j)
    (hk : ∀ x ∈ D.separator i, a x ≠ .inl k) :
    w.mass (D.side i) (.inl j) = w.mass (D.side i) (.inl k) := by
  by_cases h : j = k
  · rw [h]
  · exact w.mass_separator (u := .inl j) (v := .inl k) h
      (D.side i) (D.separator i) (D.boundary i hi) hj hk

lemma ReducedCutDecomposition.main_sides_sum (D : ReducedCutDecomposition F t)
    (w : WeightedWitness (template t) F a (starParity t)) (ht : 0 < t)
    (i : Fin D.nodes) (hi : i ≠ D.root) (j : Fin t)
    (hj : ∀ x ∈ D.separator i, a x ≠ .inl j) :
    w.mass (D.side i) (.inl j) + w.mass (D.reverseSide i) (.inl j) = 1 := by
  have hcover : (D.separator i ∪ D.side i) ∪ D.reverseSide i = Finset.univ := by
    ext x
    simp [RootedCuts.reverseSide]
  have hd : Disjoint (D.separator i ∪ D.side i) (D.reverseSide i) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  have h := w.main_mass ht j
  rw [← hcover, w.mass_union _ _ hd,
    w.mass_union _ _ (D.side_disjoint i hi).symm,
    w.mass_eq_zero _ _ hj, zero_add] at h
  exact h

/-- The sink is obtained constructively from a largest inward-pointing edge in
parent-before-child order. Empty branch indices contribute zero, as required. -/
theorem ReducedCutDecomposition.balancedStar (D : ReducedCutDecomposition F t)
    (w : WeightedWitness (template t) F a (starParity t)) (ht : 0 < t) :
    Nonempty (BalancedStar w) := by
  let P : Finset (Fin D.nodes) := Finset.univ.filter fun i => i = D.root ∨
    (i ≠ D.root ∧ ∃ j : Fin t, (∀ x ∈ D.separator i, a x ≠ .inl j) ∧
      w.mass (D.side i) (.inl j) = 1)
  have hP : P.Nonempty := ⟨D.root, by simp [P]⟩
  let i := P.max' hP
  have hiP : i ∈ P := Finset.max'_mem P hP
  have himax : ∀ j ∈ P, j ≤ i := fun j hj => Finset.le_max' P j hj
  have hzero : ∀ j (k : Fin t),
      (∀ x ∈ D.branchSeparator i j, a x ≠ .inl k) →
      w.mass (D.branch i j) (.inl k) = 0 := by
    intro j k hk
    unfold RootedCuts.branch RootedCuts.branchSeparator at *
    split_ifs at hk ⊢ with hji hir hp
    · simp [WeightedWitness.mass]
    · have hip : ∃ l : Fin t, (∀ x ∈ D.separator i, a x ≠ .inl l) ∧
          w.mass (D.side i) (.inl l) = 1 := by
        have hm : i = D.root ∨ (i ≠ D.root ∧ ∃ l : Fin t,
            (∀ x ∈ D.separator i, a x ≠ .inl l) ∧
              w.mass (D.side i) (.inl l) = 1) := (Finset.mem_filter.mp hiP).2
        exact (hm.resolve_left hir).2
      obtain ⟨l, hl, hmass⟩ := hip
      have hside : w.mass (D.side i) (.inl k) = 1 :=
        (D.main_side_equal w i hir k l hk hl).trans hmass
      have hsum := D.main_sides_sum w ht i hir k hk
      rw [hside] at hsum
      exact add_left_cancel (show 1 + w.mass (D.reverseSide i) (.inl k) = 1 + 0 by
        simpa using hsum)
    · apply (bit_zero_or_one _).resolve_right
      intro hmass
      have hjP : j ∈ P := by
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨hp.1, k, hk, hmass⟩
      have hlt := D.parent_lt j hp.1
      rw [hp.2] at hlt
      exact (not_lt_of_ge (himax j hjP)) hlt
    · simp [WeightedWitness.mass]
  exact ⟨{
    regions := D.nodes
    region := D.region i
    bag := D.bag i
    bag_eq := (D.region_none i).symm
    size := D.width i
    separator := D.branchSeparator i
    separator_sub := D.branchSeparator_sub i
    separator_small := D.branchSeparator_small ht i
    boundary := by
      intro j
      rw [D.region_some]
      exact D.branch_boundary i j
    zero_mass := by
      intro j k hk
      rw [D.region_some]
      exact hzero j k hk }⟩

/-- The helper boundary argument in reduced decomposition-cut form. -/
theorem choice_of_reducedCutDecomposition {C : ChoiceSystem t}
    (φ : F →g baseGraph C)
    (w : WeightedWitness (template t) F ((baseProjection C).comp φ) (starParity t))
    (D : ReducedCutDecomposition F t) (ht : 0 < t) : C.Successful := by
  obtain ⟨s⟩ := D.balancedStar w ht
  exact choice_of_balancedStar C φ w s ht

end DecompositionCuts

end ParityWL

end OAI
