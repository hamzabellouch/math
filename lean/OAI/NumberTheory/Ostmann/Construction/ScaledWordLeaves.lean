import OAI.NumberTheory.Ostmann.Construction.AtomSourceDescent
import OAI.NumberTheory.Ostmann.Construction.SelectedWordReversal

namespace OAI

/-! # Selected prime factors through every actual ancestor substitution -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def wordLeafScale {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) (x : TreeLeafIndex n → A) :
    CopyScheduleAtoms role n → A :=
  wordLeafAssignment role i hi n (fun v => base v.val)
    (fun t => base (wordLeafSlot role i hi n t) * x t)

theorem wordLeaf_reconstruct {I A : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) :
    wordLeafAssignment role i hi n (fun v => base v.val)
      (fun t => base (wordLeafSlot role i hi n t)) = base := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t => exact wordLeafAssignment_leaf role i hi n _ _ t
  | inr v => exact wordLeafAssignment_outside role i hi n _ _ v

theorem wordLeafScale_leaf {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) (x : TreeLeafIndex n → A) (t : TreeLeafIndex n) :
    wordLeafScale role i hi n base x (wordLeafSlot role i hi n t) =
      base (wordLeafSlot role i hi n t) * x t :=
  wordLeafAssignment_leaf role i hi n _ _ t

theorem wordLeafScale_outside {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (base : CopyScheduleAtoms role n → A) (x : TreeLeafIndex n → A)
    (v : WordLeafOutside role i hi n) :
    wordLeafScale role i hi n base x v.val = base v.val :=
  wordLeafAssignment_outside role i hi n _ _ v

/-- The inserted pivot is unchanged; only its original selected leaves scale. -/
theorem reverseCopyLabelMap_wordLeafScale {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ)
    (b : Bool) (P : A) (base : CopyScheduleAtoms role (n + 1) → A)
    (x : TreeLeafIndex (n + 1) → A) :
    reverseCopyLabelMap role n b P (wordLeafScale role i hi (n + 1) base x) =
      wordLeafScale role i hi n (reverseCopyLabelMap role n b P base)
        (fun t => x (if b then .inl t else .inr t)) := by
  funext v
  obtain ⟨v, rfl⟩ := (wordLeafPartition role i hi n).surjective v
  cases v with
  | inl t =>
    rw [wordLeafPartition_leaf, reverseCopyLabelMap_wordLeaf, wordLeafScale_leaf,
      wordLeafScale_leaf, reverseCopyLabelMap_wordLeaf]
  | inr v =>
    rw [wordLeafPartition_outside, wordLeafScale_outside]
    unfold wordLeafScale
    rw [reverseCopyLabelMap_wordOutside_independent role i hi n b P
      (fun v => base v.val) _ (fun t => base (wordLeafSlot role i hi (n + 1) t)) v,
      wordLeaf_reconstruct]

def descendLeafValues {A : Type*} : (h n : ℕ) → (Fin h → Bool) →
    (TreeLeafIndex (n + h) → A) → TreeLeafIndex n → A
  | 0, _, _, x => x
  | h + 1, n, path, x => descendLeafValues h n (Fin.tail path)
      (fun t => x (if path 0 then .inl t else .inr t))

/-- Unexposed prime factors follow precisely their own branches. -/
theorem descendAtomValues_wordLeafScale {I A : Type*} [Mul A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (h n d : ℕ) (path : Fin h → Bool) (p : ℕ → A)
    (base : CopyScheduleAtoms role (n + h) → A) (x : TreeLeafIndex (n + h) → A) :
    descendAtomValues role h n d path p (wordLeafScale role i hi (n + h) base x) =
      wordLeafScale role i hi n (descendAtomValues role h n d path p base)
        (descendLeafValues h n path x) := by
  induction h generalizing d with
  | zero => rfl
  | succ h ih =>
    change descendAtomValues role h n (d + 1) (Fin.tail path) p
      (reverseCopyLabelMap role (n + h) (path 0) (p d)
        (wordLeafScale role i hi (n + h + 1) base x)) = _
    rw [reverseCopyLabelMap_wordLeafScale, ih]
    rfl

/-- All remaining factors of the composite words stay in the coefficient. -/
theorem wordLeafScale_H_product {I A : Type*} [Fintype I] [CommMonoid A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word) (n : ℕ) (b : Bool)
    (base : CopyScheduleAtoms role (n + 1) → A) (x : TreeLeafIndex (n + 1) → A) :
    (∏ h : CopyScheduleH role n,
      wordLeafScale role i hi (n + 1) base x ⟨.inl (b, h.val), h.property⟩) =
      (∏ h : CopyScheduleH role n, base ⟨.inl (b, h.val), h.property⟩) *
        ∏ t : TreeLeafIndex n, x (if b then .inl t else .inr t) := by
  have hbase := wordLeaf_H_product role i hi n b
    (fun v => base v.val) (fun t => base (wordLeafSlot role i hi (n + 1) t))
  rw [wordLeaf_reconstruct] at hbase
  unfold wordLeafScale
  rw [wordLeaf_H_product, Finset.prod_mul_distrib, hbase]
  simp only [mul_assoc]

/-- At any internal node the H product has its original fixed/ancestor
coefficient times exactly the selected prime product below that child. -/
theorem descendAtomValues_H_product {I A : Type*} [Fintype I] [CommMonoid A]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (h n d : ℕ) (path : Fin h → Bool) (p : ℕ → A) (b : Bool)
    (base : CopyScheduleAtoms role (n + 1 + h) → A)
    (x : TreeLeafIndex (n + 1 + h) → A) :
    (∏ a : CopyScheduleH role n,
      descendAtomValues role h (n + 1) d path p
        (wordLeafScale role i hi (n + 1 + h) base x) ⟨.inl (b, a.val), a.property⟩) =
      (∏ a : CopyScheduleH role n,
        descendAtomValues role h (n + 1) d path p base ⟨.inl (b, a.val), a.property⟩) *
          ∏ t : TreeLeafIndex n, descendLeafValues h (n + 1) path x
            (if b then .inl t else .inr t) := by
  rw [descendAtomValues_wordLeafScale]
  exact wordLeafScale_H_product role i hi n b _ _

end Ostmann

end OAI
