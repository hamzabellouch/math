import OAI.Computability.PerfectCompleteness.Foundations.CutSlotAssembly

namespace OAI

section

namespace PerfectCompleteness.CutProjectionAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces MixedSupport

variable {branch : Nat → Nat} {n m t : Nat}

def castProjection {a b c d : Slot} (hab : a = b) (hcd : c = d)
    (q : Projection a c) : Projection b d := by
  cases hab
  cases hcd
  exact q

@[simp] theorem castProjection_heq {a b c d : Slot} (hab : a = b) (hcd : c = d)
    (q : Projection a c) : HEq (castProjection hab hcd q) q := by
  cases hab
  cases hcd
  rfl

def fillProjection : {n m : Nat} → (p : Path branch n m) →
    (outside : Slots branch n → Fin t → Slot) →
    (left right : Slots branch m → Fin t → Slot) →
    (∀ s k, Projection (left s k) (right s k)) →
    ∀ s k, Projection (CutSlotAssembly.fill p outside left s k)
      (CutSlotAssembly.fill p outside right s k)
  | _, _, .refl _, _, _, _, q => q
  | _, _, .step i p, outside, left, right, q => fun s k =>
      if hs : s.1 = i then
        castProjection
          (by simp only [CutSlotAssembly.fill, ite_eq_left hs])
          (by simp only [CutSlotAssembly.fill, ite_eq_left hs])
          (fillProjection p (fun j => outside (i, j)) left right q s.2 k)
      else
        castProjection
          (by simp only [CutSlotAssembly.fill, ite_eq_right hs])
          (by simp only [CutSlotAssembly.fill, ite_eq_right hs])
          (Projection.keep (outside s k))

private theorem dite_heq_of_pos {α β : Type} {P : Prop} [Decidable P]
    (f : P → α) (g : ¬ P → α) (b : β) (hP : P)
    (h : HEq (f hP) b) : HEq (dite P f g) b := by
  rw [dite_eq_left hP]
  exact h

theorem fillProjection_at_cut (p : Path branch n m)
    (outside : Slots branch n → Fin t → Slot)
    (left right : Slots branch m → Fin t → Slot)
    (q : ∀ s k, Projection (left s k) (right s k))
    (s : Slots branch m) (k : Fin t) :
    HEq (fillProjection p outside left right q (p.slotEmbedding s) k) (q s k) := by
  revert outside left right q s k
  induction p with
  | refl _ => intros; rfl
  | step i p ih =>
      intro outside left right q s k
      refine @dite_heq_of_pos _ _ (i = i) _ _ _ (q s k) rfl ?_
      exact (castProjection_heq _ _ _).trans
        (ih (fun j => outside (i, j)) left right q s k)

theorem fillProjection_at_cut_cast (p : Path branch n m)
    (outside : Slots branch n → Fin t → Slot)
    (left right : Slots branch m → Fin t → Slot)
    (q : ∀ s k, Projection (left s k) (right s k))
    (s : Slots branch m) (k : Fin t) :
    castProjection
      (congrFun (CutSlotAssembly.fill_at_cut p outside left s) k)
      (congrFun (CutSlotAssembly.fill_at_cut p outside right s) k)
      (fillProjection p outside left right q (p.slotEmbedding s) k) = q s k := by
  apply eq_of_heq
  exact (castProjection_heq _ _ _).trans (fillProjection_at_cut p outside left right q s k)

end
end PerfectCompleteness.CutProjectionAssembly

end

end OAI
