import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace OAI

/-! # Component Indices -/

noncomputable section
namespace HadwigerCounterexample

abbrev Tag := Fin
abbrev Comp (g : ℕ) := { p : Tag g × Tag g // p.1 < p.2 }

variable {g : ℕ}

def edge (l d : Tag g) (h : l ≠ d) : Comp g :=
  if hl : l < d then ⟨(l,d),hl⟩ else ⟨(d,l),lt_of_le_of_ne (le_of_not_gt hl) h.symm⟩

theorem edge_eq {l d : Tag g} (h : l < d) : edge l d (ne_of_lt h) = ⟨(l,d),h⟩ := by
  simp [edge,h]

theorem edge_symm {l d : Tag g} (h : l ≠ d) : edge l d h = edge d l h.symm := by
  rcases lt_or_gt_of_ne h with e|e
  · simp [edge,e,not_lt.mpr e.le]
  · simp [edge,e,not_lt.mpr e.le]

def inc (e : Comp g) (l : Tag g) : Prop := e.val.1 = l ∨ e.val.2 = l
instance (e : Comp g) (l : Tag g) : Decidable (inc e l) := inferInstanceAs (Decidable (_ ∨ _))

theorem inc_edge_fst {l d : Tag g} (h : l ≠ d) : inc (edge l d h) l := by
  by_cases e : l < d <;> simp [inc,edge,e]

theorem inc_edge_iff {l d x : Tag g} (h : l ≠ d) : inc (edge l d h) x ↔ (l=x ∨ d=x) := by
  by_cases e : l < d <;> simp [inc,edge,e,or_comm]

abbrev TagStar (l : Tag g) := {e : Comp g // inc e l}

def starEquiv (l : Tag g) : {d : Tag g // l ≠ d} ≃ TagStar l := by
  let f (d : {d : Tag g // l ≠ d}) : TagStar l := ⟨edge l d d.property,inc_edge_fst _⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    have hi : inc (edge l i i.property) i := (inc_edge_iff _).mpr (Or.inr rfl)
    change inc (f i).val i at hi
    rw [h] at hi
    exact Subtype.ext (((inc_edge_iff j.property).mp hi).resolve_left i.property).symm
  · rintro ⟨⟨⟨i,j⟩,hij⟩,he⟩
    rcases he with g|g
    · change i = l at g
      subst l
      refine ⟨⟨j,hij.ne⟩,Subtype.ext ?_⟩
      exact edge_eq hij
    · change j = l at g
      subst l
      refine ⟨⟨i,hij.ne.symm⟩,Subtype.ext ?_⟩
      dsimp only [f]
      rw [edge_symm,edge_eq hij]

theorem card_star (l : Tag g) : Fintype.card (TagStar l) = g - 1 := by
  rw [← Fintype.card_congr (starEquiv l)]
  exact (Fintype.card_subtype_compl (fun d => l=d)).trans (by simp)

/-- l in I_d. -/
def allowed (d l : Tag g) :=
  0 < (l-d).val ∧ (l-d).val ≤ (g-1)/2

instance (d l : Tag g) : Decidable (allowed d l) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem not_allowed (d : Tag g) : ¬allowed d d := by
  have : NeZero g := ⟨by have := d.isLt; omega⟩
  simp [allowed]

theorem card_allowed (d : Tag g) : Fintype.card {l : Tag g // allowed d l} = (g-1)/2 := by
  have : NeZero g := ⟨by have := d.isLt; omega⟩
  let T := {l : Tag g // allowed d l}
  let f (i : Fin ((g-1)/2)) : Tag g := ⟨i.val+1,by have := i.isLt; omega⟩
  have hf (i) : allowed d (f i + d) := by
    have := i.isLt
    simp only [allowed,add_sub_cancel_right,f]
    omega
  let h : Fin ((g-1)/2) → T := fun i => ⟨f i + d,hf i⟩
  have hh : Function.Bijective h := by
    constructor
    · intro i j hij
      have he : f i = f j := add_right_cancel (congrArg Subtype.val hij)
      have he' := congrArg Fin.val he
      exact Fin.ext (Nat.add_right_cancel he')
    · intro l
      have hl := l.property
      unfold allowed at hl
      let i : Fin ((g-1)/2) := ⟨(l.val-d).val-1,by omega⟩
      have hi : f i = l.val-d := Fin.ext (by dsimp only [i,f]; omega)
      refine ⟨i,Subtype.ext ?_⟩
      change f i + d = _
      rw [hi,sub_add_cancel]
  simpa using (Fintype.card_congr (Equiv.ofBijective h hh)).symm

theorem card_allowed' (l : Tag g) :
    Fintype.card {d : Tag g // allowed d l} = (g-1)/2 := by
  have : NeZero g := ⟨by have := l.isLt; omega⟩
  let h : {d : Tag g // allowed d l} ≃ {x : Tag g // allowed 0 x} := {
    toFun := fun d => ⟨l-d.val, by simpa only [allowed,sub_zero] using d.property⟩
    invFun := fun x => ⟨l-x.val, by simpa only [allowed,sub_sub_cancel,sub_zero] using
      x.property⟩
    left_inv := fun d => Subtype.ext (sub_sub_cancel _ _)
    right_inv := fun x => Subtype.ext (sub_sub_cancel _ _) }
  exact (Fintype.card_congr h).trans (card_allowed _)

end HadwigerCounterexample

end

end OAI
