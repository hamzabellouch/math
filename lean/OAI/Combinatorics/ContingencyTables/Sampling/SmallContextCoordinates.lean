import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextFibres
import OAI.Combinatorics.ContingencyTables.Rooted.LargePairEnumeration

namespace OAI

/-! # Actual row-major small-prefix coordinate splitting

The retained prefix is precisely the earlier small cells. The remaining
ordinary cells all follow the next exposed cell, which is the condition
needed for the completion-retaining conditional repair injection.
-/

namespace ContingencyTables.SmallContextCoordinates

open scoped Classical
open LargePairEnumeration BalancedFamily

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma rowMajor_trichotomy (s t : I×J) : RowMajorBefore s t ∨ s=t ∨ RowMajorBefore t s := by
  rcases lt_trichotomy s.1 t.1 with h|h|h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy s.2 t.2 with hc|hc|hc
    · exact Or.inl (Or.inr ⟨h,hc⟩)
    · exact Or.inr (Or.inl (Prod.ext h hc))
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm,hc⟩))
  · exact Or.inr (Or.inr (Or.inl h))

abbrev Cells (small : I → J → Bool) := {a : I×J // small a.1 a.2=true}

def Earlier (small : I → J → Bool) (s : I×J) := {a : Cells small // RowMajorBefore a.val s}
def Later (small : I → J → Bool) (s : I×J) := {a : Cells small // RowMajorBefore s a.val}

noncomputable instance earlierFintype [Fintype I] [Fintype J]
    (small : I → J → Bool) (s : I×J) : Fintype (Earlier small s) := by
  unfold Earlier
  infer_instance

noncomputable instance laterFintype [Fintype I] [Fintype J]
    (small : I → J → Bool) (s : I×J) : Fintype (Later small s) := by
  unfold Later
  infer_instance

noncomputable def cellSplitEquiv (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) :
    (Earlier small s ⊕ (Unit ⊕ Later small s)) ≃ Cells small where
  toFun
    | .inl a => a.val
    | .inr (.inl _) => ⟨s,hs⟩
    | .inr (.inr a) => a.val
  invFun a :=
    if hp : RowMajorBefore a.val s then .inl ⟨a,hp⟩
    else if he : a.val=s then .inr (.inl ())
    else .inr (.inr ⟨a,by
      rcases rowMajor_trichotomy a.val s with h|h|h
      · exact False.elim (hp h)
      · exact False.elim (he h)
      · exact h⟩)
  left_inv a := by
    cases a with
    | inl a =>
      simp only [dite_eq_left a.property]
      exact congrArg Sum.inl (Subtype.ext rfl)
    | inr a =>
      cases a with
      | inl a =>
        cases a
        have hp : ¬RowMajorBefore s s := fun h => h.ne rfl
        simp only [dite_eq_right hp,↓reduceDIte]
      | inr a =>
        have hp : ¬RowMajorBefore a.val.val s := fun h => (h.trans a.property).ne rfl
        have he : a.val.val≠s := a.property.ne.symm
        simp only [dite_eq_right hp,dite_eq_right he]
        exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext rfl))
  right_inv a := by
    by_cases hp : RowMajorBefore a.val s
    · simp only [dite_eq_left hp]
    · by_cases he : a.val=s
      · simp only [dite_eq_right hp,dite_eq_left he]
        exact Subtype.ext he.symm
      · simp only [dite_eq_right hp,dite_eq_right he]

/-- Pack the prefix, special pair and suffix into the cell split. -/
def splitPairEquiv (P T : Type u) :
    ((P×Bool) ⊕ (Bool ⊕ (T×Bool))) ≃ (P ⊕ (Unit ⊕ T))×Bool where
  toFun
    | .inl (p,b) => (.inl p,b)
    | .inr (.inl b) => (.inr (.inl ()),b)
    | .inr (.inr (t,b)) => (.inr (.inr t),b)
  invFun
    | (.inl p,b) => .inl (p,b)
    | (.inr (.inl _),b) => .inr (.inl b)
    | (.inr (.inr t),b) => .inr (.inr (t,b))
  left_inv x := by rcases x with ⟨p,b⟩|b|⟨t,b⟩ <;> rfl
  right_inv x := by rcases x with ⟨p|(_|t),b⟩ <;> rfl

/-- The exact small-coordinate bijection required by physical context
transport. The suffix enumeration introduces no extra assignment. -/
noncomputable def contextEquiv (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ) :
    ((Earlier small s×Bool) ⊕ Coordinates Bool (widths (fun _ : Fin n => U))) ≃
      SmallView (fun a : I×J => small a.1 a.2) :=
  (Equiv.sumCongr (Equiv.refl _) ((coordinateEquiv Bool (fun _ : Fin n => U)).trans
    (Equiv.sumCongr (Equiv.refl Bool) (e.prodCongr (Equiv.refl Bool))))).trans
      ((splitPairEquiv _ _).trans ((cellSplitEquiv small s hs).prodCongr (Equiv.refl Bool)))

lemma contextEquiv_prefix (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ)
    (a : Earlier small s) (b : Bool) :
    contextEquiv small s hs e U (.inl (a,b))=(a.val,b) := rfl

lemma contextEquiv_special (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ) (b : Bool) :
    contextEquiv small s hs e U
      (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inl b)))=(⟨s,hs⟩,b) := by
  simp only [contextEquiv,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inr,Sum.map_inl,Equiv.refl_apply,
    Equiv.apply_symm_apply]
  rfl

lemma contextEquiv_later (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) {n : ℕ} (e : Fin n ≃ Later small s) (U : ℕ)
    (a : Fin n) (b : Bool) :
    contextEquiv small s hs e U
      (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inr (a,b))))=((e a).val,b) := by
  simp only [contextEquiv,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inr,
    Equiv.apply_symm_apply]
  rfl

end ContingencyTables.SmallContextCoordinates

end OAI
