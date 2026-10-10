import OAI.Combinatorics.ParityLifts.Detection

namespace OAI

namespace ParityWL

open scoped BigOperators

section RankedTrees

open scoped Classical

structure RankedTree (N : Type) where
  root : N
  parent : N → N
  rank : N → ℕ
  parent_lt : ∀ i, i ≠ root → rank (parent i) < rank i

inductive RankedTree.Ancestor {N : Type} (D : RankedTree N) (i : N) : N → Prop
  | refl : D.Ancestor i i
  | step {j : N} (hj : j ≠ D.root) : D.Ancestor i (D.parent j) → D.Ancestor i j

namespace RankedTree

variable {N : Type} (D : RankedTree N)

lemma Ancestor.trans {i j k : N} (h : D.Ancestor i j) (g : D.Ancestor j k) :
    D.Ancestor i k := by
  induction g with
  | refl => exact h
  | step hk g ih => exact .step hk ih

lemma Ancestor.cases' {i j : N} (h : D.Ancestor i j) :
    i = j ∨ (j ≠ D.root ∧ D.Ancestor i (D.parent j)) := by
  cases h with
  | refl => exact Or.inl rfl
  | step h g => exact Or.inr ⟨h, g⟩

lemma root_ancestor (j : N) : D.Ancestor D.root j := by
  by_cases h : j = D.root
  · subst j; exact .refl
  · exact .step h (root_ancestor (D.parent j))
termination_by D.rank j
decreasing_by exact D.parent_lt j h

theorem Ancestor.map {M : Type} (E : RankedTree M) (f : N → M)
    (hstep : ∀ j, j ≠ D.root → E.Ancestor (f (D.parent j)) (f j))
    {i j : N} (h : D.Ancestor i j) : E.Ancestor (f i) (f j) := by
  induction h with
  | refl => exact .refl
  | @step j hj h ih => exact ih.trans E (hstep j hj)

variable [Fintype N]

@[instance_reducible] noncomputable def nodeOrder : LinearOrder N :=
  LinearOrder.lift' (fun i => (toLex (D.rank i, (Fintype.equivFin N i).val))) (by
    intro i j h
    have he : Fintype.equivFin N i = Fintype.equivFin N j := Fin.ext
      (congrArg (fun p : Lex (ℕ × ℕ) => (ofLex p).2) h)
    exact (Fintype.equivFin N).injective he)

noncomputable def enumeration : Fin (Fintype.card N) ≃ N := by
  letI := D.nodeOrder
  exact (Fintype.orderIsoFinOfCardEq N rfl).toEquiv

noncomputable def indexed : IndexedTree where
  nodes := Fintype.card N
  root := D.enumeration.symm D.root
  parent i := D.enumeration.symm (D.parent (D.enumeration i))
  parent_lt i hi := by
    let := D.nodeOrder
    change (Fintype.orderIsoFinOfCardEq N rfl).symm
      (D.parent ((Fintype.orderIsoFinOfCardEq N rfl) i)) < i
    rw [OrderIso.symm_apply_lt]
    change Prod.Lex (· < ·) (· < ·)
      (D.rank (D.parent _), _) (D.rank _, _)
    apply Prod.Lex.left
    apply D.parent_lt
    intro he
    apply hi
    apply D.enumeration.injective
    simpa only [enumeration, Equiv.apply_symm_apply, OrderIso.coe_toEquiv] using he

lemma ancestor_indexed {i j : N} (h : D.Ancestor i j) :
    D.indexed.Ancestor (D.enumeration.symm i) (D.enumeration.symm j) := by
  induction h with
  | refl => exact .refl
  | @step j hj h ih =>
    apply IndexedTree.Ancestor.step
    · intro he
      apply hj
      exact D.enumeration.symm.injective he
    · simpa only [indexed, Equiv.apply_symm_apply] using ih

lemma indexed_ancestor {i j : Fin (Fintype.card N)} (h : D.indexed.Ancestor i j) :
    D.Ancestor (D.enumeration i) (D.enumeration j) := by
  have hm : ∀ (T : IndexedTree) (f : Fin T.nodes → N),
      (∀ j, j ≠ T.root → D.Ancestor (f (T.parent j)) (f j)) →
      ∀ i j, T.Ancestor i j → D.Ancestor (f i) (f j) := by
    intro T f hf i j h
    induction h with
    | refl => exact .refl
    | @step j hj h ih => exact ih.trans D (hf j hj)
  apply hm D.indexed D.enumeration _ i j h
  intro j hj
  apply Ancestor.step
  · intro he
    apply hj
    apply D.enumeration.injective
    simpa only [indexed, Equiv.apply_symm_apply] using he
  · simp only [indexed, Equiv.apply_symm_apply]
    exact .refl

end RankedTree

/-- This records ordinary bag axioms, not lift solvability or any WL promise. -/
structure RankedBagTree {W N : Type} (R : W → W → Prop) (t : ℕ) extends RankedTree N where
  bag : N → Finset W
  top : W → N
  top_mem : ∀ x, x ∈ bag (top x)
  top_ancestor : ∀ x i, x ∈ bag i → toRankedTree.Ancestor (top x) i
  interval_mem : ∀ x i j, toRankedTree.Ancestor (top x) i →
    toRankedTree.Ancestor i j → x ∈ bag j → x ∈ bag i
  edge_cover : ∀ x y, R x y → ∃ i, x ∈ bag i ∧ y ∈ bag i
  width : ∀ i, (bag i).card ≤ t
  intersection : ∀ i, i ≠ root → (bag i ∩ bag (parent i)).card < t

namespace RankedBagTree

variable {W N : Type} [Fintype W] [Fintype N] {F : SimpleGraph W} {t : ℕ}

noncomputable def toIndexed (D : RankedBagTree (N := N) F.Adj t) : ReducedBagTree F t where
  toIndexedTree := D.toRankedTree.indexed
  bag i := D.bag (D.toRankedTree.enumeration i)
  top x := D.toRankedTree.enumeration.symm (D.top x)
  top_mem x := by simp only [Equiv.apply_symm_apply]; exact D.top_mem x
  top_ancestor x i hx := by
    change Fin (Fintype.card N) at i
    simpa only [RankedTree.indexed, Equiv.symm_apply_apply] using
      D.toRankedTree.ancestor_indexed (D.top_ancestor x _ hx)
  interval_mem x i j hi hij hx := by
    apply D.interval_mem x _ _ _ (D.toRankedTree.indexed_ancestor hij) hx
    simpa only [Equiv.apply_symm_apply] using D.toRankedTree.indexed_ancestor hi
  edge_cover x y h := by
    obtain ⟨i, hx, hy⟩ := D.edge_cover x y h
    exact ⟨D.toRankedTree.enumeration.symm i, by simpa, by simpa⟩
  width i := D.width _
  intersection i hi := by
    simp only [RankedTree.indexed, Equiv.apply_symm_apply]
    apply D.intersection
    intro he
    apply hi
    apply D.toRankedTree.enumeration.injective
    simpa only [RankedTree.indexed, Equiv.apply_symm_apply] using he

end RankedBagTree

/-- Equality for every genuinely decomposed uncolored source. -/
theorem no_choice_equal_decomposed {W N : Type} [Fintype W] [Fintype N]
    {t : ℕ} (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful)
    (F : SimpleGraph W) (D : RankedBagTree (N := N) F.Adj t) :
    homCount F (zeroLift C) = homCount F (starLift C) := by
  apply le_antisymm
  · by_contra h
    have hlt : homCount F (starLift C) < homCount F (zeroLift C) := by omega
    obtain ⟨φ, ⟨w⟩⟩ := homCount_lift_strict_iff_witness.mp hlt
    exact hn (choice_of_reducedCutDecomposition φ w D.toIndexed.toReducedCuts ht)
  · exact homCount_lift_le _ _ _ _ _

end RankedTrees

end ParityWL

end OAI
