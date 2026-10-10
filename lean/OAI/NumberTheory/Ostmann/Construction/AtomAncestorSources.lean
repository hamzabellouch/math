import OAI.NumberTheory.Ostmann.Construction.ReverseAtomSources
import OAI.NumberTheory.Ostmann.Construction.AncestorPivotPrecision

namespace OAI

/-! # Constructing finite ancestor products from distinct atom sources -/

namespace Ostmann
open scoped BigOperators Classical

def atomSourceExtend {B : Type*} (d : ℕ) : B ⊕ Fin d ↪ B ⊕ Fin (d + 1) where
  toFun
    | .inl b => .inl b
    | .inr j => .inr j.castSucc
  inj' := by
    intro a b h
    cases a <;> cases b
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · cases h
    · cases h
    · rename_i a b
      have hh : (Sum.inr a.castSucc : B ⊕ Fin (d + 1)) = .inr b.castSucc := h
      have he : a.castSucc = b.castSucc := Sum.inr.inj hh
      have hv : a.val = b.val := congrArg (fun j : Fin (d + 1) => j.val) he
      exact congrArg Sum.inr (Fin.ext hv)

theorem atomSourceExtend_ne_last {B : Type*} (d : ℕ) (a : B ⊕ Fin d) :
    atomSourceExtend d a ≠ .inr (Fin.last d) := by
  cases a with
  | inl b => intro h; cases h
  | inr j =>
    intro h
    have hv := congrArg Fin.val (Sum.inr.inj h)
    change j.val = d at hv
    exact Nat.ne_of_lt j.isLt hv

noncomputable def advanceAtomSources {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ Fin d) :
    CopyScheduleAtoms role n → B ⊕ Fin (d + 1) :=
  reverseCopyLabelMap role n b (.inr (Fin.last d)) (fun v => atomSourceExtend d (source v))

theorem advanceAtomSources_injective {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ Fin d)
    (hs : Function.Injective source)
    (hu : ∀ i j, role i = .pivot n → role j = .pivot n → i = j) :
    Function.Injective (advanceAtomSources role n d b source) :=
  reverseCopyLabelMap_injective role n b hu _ _ ((atomSourceExtend d).injective.comp hs)
    (fun v => atomSourceExtend_ne_last d (source v))

theorem reverseCopyLabelMap_map {I A B : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : A) (current : CopyScheduleAtoms role (n + 1) → A)
    (f : A → B) (v : CopyScheduleAtoms role n) :
    f (reverseCopyLabelMap role n b P current v) =
      reverseCopyLabelMap role n b (f P) (fun w => f (current w)) v := by
  unfold reverseCopyLabelMap
  split_ifs <;> rfl

theorem atomSourceExtend_eval {B A : Type*} (d : ℕ) (C : B → A) (p : Fin (d + 1) → A)
    (s : B ⊕ Fin d) :
    Sum.elim C p (atomSourceExtend d s) = Sum.elim C (fun j => p j.castSucc) s := by
  cases s <;> rfl

/-- Source evaluation gives the actual reverse assignment, including the
newly inserted integral pivot. Earlier pivots retain their original indices. -/
theorem advanceAtomSources_eval {I B A : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ Fin d)
    (C : B → A) (p : Fin (d + 1) → A) (v : CopyScheduleAtoms role n) :
    Sum.elim C p (advanceAtomSources role n d b source v) =
      reverseCopyLabelMap role n b (p (Fin.last d))
        (fun w => Sum.elim C (fun j => p j.castSucc) (source w)) v := by
  unfold advanceAtomSources
  rw [reverseCopyLabelMap_map role n b (.inr (Fin.last d))
    (fun w => atomSourceExtend d (source w)) (Sum.elim C p) v]
  simp only [Sum.elim_inr, atomSourceExtend_eval]

noncomputable def atomAncestorSet {A B : Type*} [Fintype A] {d : ℕ}
    (source : A → B ⊕ Fin d) : Finset (Fin d) :=
  (Finset.univ.image source).toRight

noncomputable def atomFixedProduct {A B : Type*} [Fintype A] {d : ℕ}
    (source : A → B ⊕ Fin d) (C : B → ℤ) : ℤ :=
  ∏ b ∈ (Finset.univ.image source).toLeft, C b

/-- No multiplicity bound is postulated: source injectivity gives exactly
the finite set product used by PivotDependencyScheme. -/
theorem atomSource_product {A B : Type*} [Fintype A] {d : ℕ}
    (source : A → B ⊕ Fin d) (hs : Function.Injective source)
    (C : B → ℤ) (p : Fin d → ℤ) :
    (∏ a, Sum.elim C p (source a)) =
      ancestorCoefficient (atomFixedProduct source C) (atomAncestorSet source) p := by
  rw [← Finset.prod_image (fun a _ b _ h => hs h)]
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  rfl

end Ostmann

end OAI
