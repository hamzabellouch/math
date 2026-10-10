import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateProducts

namespace OAI

/-! # The two independent surviving regular templates -/

namespace Ostmann
open scoped Classical BigOperators

def movingTemplatePairEquiv (n r m : ℕ) :
    MovingRegularSlot n r m ⊕ MovingRegularSlot n r m ≃ MovingRegularSlot (n + 1) r m :=
  (Equiv.sumProdDistrib (TreeLeafIndex n) (TreeLeafIndex n) (Fin r ⊕ Fin m)).symm

noncomputable def movingTemplatePairSample {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) : MovingRegularSlot (n + 1) r m → A :=
  Sum.elim left right ∘ (movingTemplatePairEquiv n r m).symm

@[simp] theorem movingTemplatePairSample_left {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) (j : MovingRegularSlot n r m) :
    movingTemplatePairSample n r m left right (.inl j.1, j.2) = left j := rfl

@[simp] theorem movingTemplatePairSample_right {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) (j : MovingRegularSlot n r m) :
    movingTemplatePairSample n r m left right (.inr j.1, j.2) = right j := rfl

theorem movingTemplatePairSample_small {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingTemplatePairSample n r m left right)) (n + 1)
      (movingTemplateSmall (n + 1) r m) =
      (treeLeafMap (List.map left) n (movingTemplateSmall n r m),
        treeLeafMap (List.map right) n (movingTemplateSmall n r m)) := by
  apply (treeLeafTupleEquiv (List A) (n + 1)).injective
  funext j
  rw [treeLeafTupleEquiv_map]
  cases j with
  | inl j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map left) n (movingTemplateSmall n r m)) j
    rw [treeLeafTupleEquiv_map]
    simp only [movingTemplateSmall, bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl
  | inr j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map right) n (movingTemplateSmall n r m)) j
    rw [treeLeafTupleEquiv_map]
    simp only [movingTemplateSmall, bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl

theorem movingTemplatePairSample_bulk {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) :
    treeLeafMap (List.map (movingTemplatePairSample n r m left right)) (n + 1)
      (bulkSlotLeaves (n + 1) m (movingTemplateBulk (n + 1) r m)) =
      (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m)),
        treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) := by
  apply (treeLeafTupleEquiv (List A) (n + 1)).injective
  funext j
  rw [treeLeafTupleEquiv_map]
  cases j with
  | inl j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map left) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) j
    rw [treeLeafTupleEquiv_map]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl
  | inr j =>
    change _ = treeLeafTupleEquiv (List A) n
      (treeLeafMap (List.map right) n (bulkSlotLeaves n m (movingTemplateBulk n r m))) j
    rw [treeLeafTupleEquiv_map]
    simp only [bulkSlotLeaves, Equiv.apply_symm_apply, List.map_ofFn]
    rfl

private theorem finite_prior_sum_type {J K A : Type*}
    [Fintype J] [Fintype K] [Fintype A] (ν : J ⊕ K → A → ℝ)
    (F : (J ⊕ K → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ l : J → A, ((∏ i, ν (.inl i) (l i) : ℝ) : ℂ) *
        ∑ r : K → A, ((∏ i, ν (.inr i) (r i) : ℝ) : ℂ) * F (Sum.elim l r) := by
  let e := Equiv.sumArrowEquivProdArrow J K A
  rw [← e.symm.sum_comp (fun x => ((∏ i, ν i (x i) : ℝ) : ℂ) * F x),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.prod_sum_type]
  simp only [e, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr, Complex.ofReal_mul]
  exact mul_assoc _ _ _

/-- Pairing surviving templates preserves the independent law. The shared
compensation law stays outside this identity. -/
theorem movingTemplatePair_average {A : Type*} [Fintype A] (n r m : ℕ)
    (ν : MovingRegularSlot (n + 1) r m → A → ℝ)
    (F : (MovingRegularSlot (n + 1) r m → A) → ℂ) :
    (∑ x, ((∏ i, ν i (x i) : ℝ) : ℂ) * F x) =
      ∑ left : MovingRegularSlot n r m → A,
        ((∏ i, ν (.inl i.1, i.2) (left i) : ℝ) : ℂ) *
          ∑ right : MovingRegularSlot n r m → A,
            ((∏ i, ν (.inr i.1, i.2) (right i) : ℝ) : ℂ) *
              F (movingTemplatePairSample n r m left right) := by
  have hr := finite_prior_reindex (movingTemplatePairEquiv n r m) ν F
  simp only [finite_univ_canonical] at hr ⊢
  rw [← hr]
  have hs := finite_prior_sum_type (fun i => ν (movingTemplatePairEquiv n r m i))
    (fun x => F (x ∘ (movingTemplatePairEquiv n r m).symm))
  simp only [finite_univ_canonical] at hs
  exact hs

end Ostmann

end OAI
