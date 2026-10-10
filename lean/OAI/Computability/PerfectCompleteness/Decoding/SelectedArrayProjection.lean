import OAI.Computability.PerfectCompleteness.Decoding.CutGroupedProjectionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas

namespace OAI

section

namespace PerfectCompleteness.SelectedArrayProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit SelectedArrayReplacement
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem selectedRows_pullback (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (arrays : Arrays right rows),
      selectedRows rows p left (ChildBlockProjection.arraysPullback rows q arrays) =
        fun row => HPullback (CutGroupedProjection.cutProjection p q)
          (selectedRows rows p right arrays row) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro left right q arrays; rfl
      | step i p =>
          intro left right q arrays
          exact ih p (childSlots left i) (childSlots right i)
            (ChildAssemblyProjection.childProjection q i)
            (fun node => arrays (.inr (i, node)))

private theorem replace_selected (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots))
    (node : Nodes branch n) :
    replace rows (.step i p) slots arrays fresh (.inr (i, node)) =
      replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh node :=
  congrFun (WholeArraySampler.childrenAt_selected slots rows i
    (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
    (fun child v => arrays (.inr (child.val, v)))) node

private theorem replace_ordinary (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots))
    (child : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    replace rows (.step i p) slots arrays fresh (.inr (child.val, node)) =
      arrays (.inr (child.val, node)) :=
  congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
    (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
    (fun j v => arrays (.inr (j.val, v))) child) node

theorem replace_pullback (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (arrays : Arrays right rows)
      (fresh : Fin (rows (m + 1)) → H (subtreeSlots p right)),
      replace rows p left (ChildBlockProjection.arraysPullback rows q arrays)
          (fun row => HPullback (CutGroupedProjection.cutProjection p q) (fresh row)) =
        ChildBlockProjection.arraysPullback rows q (replace rows p right arrays fresh) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q arrays fresh
          funext node row
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · rfl
      | step i p =>
          intro left right q arrays fresh
          funext node row
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · change replace rows (.step i p) left
                (ChildBlockProjection.arraysPullback rows q arrays)
                (fun row => HPullback (CutGroupedProjection.cutProjection (.step i p) q)
                  (fresh row)) (.inr (child, node)) row =
              HPullback (ChildBlockProjection.nodeProjection q (.inr (child, node)))
                (replace rows (.step i p) right arrays fresh (.inr (child, node)) row)
            by_cases hchild : child = i
            · subst child
              rw [replace_selected, replace_selected]
              exact congrFun (congrFun
                (ih p (childSlots left i) (childSlots right i)
                  (ChildAssemblyProjection.childProjection q i)
                  (fun node => arrays (.inr (i, node))) fresh) node) row
            · rw [replace_ordinary rows i p left _ _ ⟨child, hchild⟩ node,
                replace_ordinary rows i p right arrays fresh ⟨child, hchild⟩ node]
              rfl

end
end PerfectCompleteness.SelectedArrayProjection

end

end OAI
