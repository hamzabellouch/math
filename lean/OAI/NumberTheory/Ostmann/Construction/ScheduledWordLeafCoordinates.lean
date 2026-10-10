import Mathlib.Logic.Equiv.Set
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalComparison
import OAI.NumberTheory.Ostmann.Characters.TreeLeafIndex

namespace OAI

/-! # One original word-prime coordinate at each arithmetic tree leaf -/

namespace Ostmann
open scoped BigOperators Classical

/-- Left arithmetic children use the positive copy of H. -/
def treeLeafCopyPath : (n : ℕ) → TreeLeafIndex n → Fin n → Bool
  | 0, _ => fun j => Fin.elim0 j
  | n + 1, .inl t => Fin.snoc (treeLeafCopyPath n t) true
  | n + 1, .inr t => Fin.snoc (treeLeafCopyPath n t) false

theorem treeLeafCopyPath_injective (n : ℕ) : Function.Injective (treeLeafCopyPath n) := by
  induction n with
  | zero =>
    intro x y _
    exact @Subsingleton.elim Unit _ x y
  | succ n ih =>
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply ih
        funext j
        simpa only [treeLeafCopyPath, Fin.snoc_castSucc] using congrFun h j.castSucc
      | inr y =>
        have hh := congrFun h (Fin.last n)
        simp only [treeLeafCopyPath, Fin.snoc_last] at hh
        cases hh
    | inr x =>
      cases y with
      | inl y =>
        have hh := congrFun h (Fin.last n)
        simp only [treeLeafCopyPath, Fin.snoc_last] at hh
        cases hh
      | inr y =>
        apply congrArg Sum.inr
        apply ih
        funext j
        simpa only [treeLeafCopyPath, Fin.snoc_castSucc] using congrFun h j.castSucc

noncomputable def wordLeafSlot {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) : TreeLeafIndex n ↪ CopyScheduleAtoms role n where
  toFun t := ⟨copySchedulePath n (treeLeafCopyPath n t) i,
    copyScheduleSurvives_path role i hi n _⟩
  inj' := by
    intro x y h
    apply treeLeafCopyPath_injective n
    exact congrArg Prod.fst (copySchedulePath_injective n
      (a₁ := (treeLeafCopyPath n x, i)) (a₂ := (treeLeafCopyPath n y, i))
      (congrArg Subtype.val h))

theorem wordLeafSlot_origin {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    copyScheduleOrigin n (wordLeafSlot role i hi n t).val = i :=
  copyScheduleOrigin_path n _ i

theorem wordLeafSlot_role {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    copyScheduleRole role n (wordLeafSlot role i hi n t).val = .word :=
  copyScheduleRole_path role i hi n _

theorem wordLeafSlot_left {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    (wordLeafSlot role i hi (n + 1) (.inl t)).val =
      .inl (true, (wordLeafSlot role i hi n t).val) := by
  exact copySchedulePath_snoc _ _ _

theorem wordLeafSlot_right {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    (wordLeafSlot role i hi (n + 1) (.inr t)).val =
      .inl (false, (wordLeafSlot role i hi n t).val) := by
  exact copySchedulePath_snoc _ _ _

/-- Reversal reads exactly the corresponding leaf prime; the inserted pivot
does not replace any of the chosen word coordinates. -/
theorem reverseCopyLabelMap_wordLeaf {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (b : Bool) (p : A)
    (x : CopyScheduleAtoms role (n + 1) → A) (t : TreeLeafIndex n) :
    reverseCopyLabelMap role n b p x (wordLeafSlot role i hi n t) =
      x (wordLeafSlot role i hi (n + 1) (if b then .inl t else .inr t)) := by
  have hc : (copyScheduleRole role n (wordLeafSlot role i hi n t).val).copiedAt n = true := by
    rw [wordLeafSlot_role]
    rfl
  rw [reverseCopyLabelMap, dite_eq_left hc]
  congr 1
  apply Subtype.ext
  cases b
  · exact (wordLeafSlot_right role i hi n t).symm
  · exact (wordLeafSlot_left role i hi n t).symm

abbrev WordLeafOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :=
  {v : CopyScheduleAtoms role n // v ∉ Set.range (wordLeafSlot role i hi n)}

noncomputable def wordLeafPartition {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :
    TreeLeafIndex n ⊕ WordLeafOutside role i hi n ≃ CopyScheduleAtoms role n :=
  (Equiv.sumCongr (Equiv.ofInjective _ (wordLeafSlot role i hi n).injective)
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (wordLeafSlot role i hi n)))

theorem wordLeafPartition_leaf {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    wordLeafPartition role i hi n (.inl t) = wordLeafSlot role i hi n t := rfl

theorem wordLeafPartition_outside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (v : WordLeafOutside role i hi n) :
    wordLeafPartition role i hi n (.inr v) = v.val := rfl

noncomputable def wordLeafAssignment {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) :
    CopyScheduleAtoms role n → A :=
  fun v => Sum.elim x y ((wordLeafPartition role i hi n).symm v)

@[simp] theorem wordLeafAssignment_leaf {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) (t : TreeLeafIndex n) :
    wordLeafAssignment role i hi n y x (wordLeafSlot role i hi n t) = x t := by
  change Sum.elim x y ((wordLeafPartition role i hi n).symm
    (wordLeafPartition role i hi n (.inl t))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem wordLeafAssignment_outside {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A)
    (v : WordLeafOutside role i hi n) : wordLeafAssignment role i hi n y x v.val = y v := by
  change Sum.elim x y ((wordLeafPartition role i hi n).symm
    (wordLeafPartition role i hi n (.inr v))) = _
  rw [Equiv.symm_apply_apply]
  rfl

noncomputable def wordLeafAssignmentEquiv {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :
    ((WordLeafOutside role i hi n → A) × (TreeLeafIndex n → A)) ≃
      (CopyScheduleAtoms role n → A) where
  toFun z := wordLeafAssignment role i hi n z.1 z.2
  invFun q := (fun v => q v.val, fun t => q (wordLeafSlot role i hi n t))
  left_inv z := by
    apply Prod.ext <;> funext v <;> simp
  right_inv q := by
    funext v
    obtain ⟨z, rfl⟩ := (wordLeafPartition role i hi n).surjective v
    cases z with
    | inl t => exact wordLeafAssignment_leaf role i hi n _ _ t
    | inr v => exact wordLeafAssignment_outside role i hi n _ _ v

theorem scheduledPrimePrior_wordLeaf {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (μ : I → A → ℝ) (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) :
    scheduledPrimePrior role n μ (wordLeafAssignment role i hi n y x) =
      (∏ v : WordLeafOutside role i hi n, μ (copyScheduleOrigin n v.val.val) (y v)) *
        ∏ t, μ i (x t) := by
  unfold scheduledPrimePrior
  rw [← (wordLeafPartition role i hi n).prod_comp]
  rw [Fintype.prod_sum_type]
  simp only [wordLeafPartition_leaf, wordLeafPartition_outside,
    wordLeafAssignment_leaf, wordLeafAssignment_outside, wordLeafSlot_origin]
  exact mul_comm _ _

end Ostmann

end OAI
