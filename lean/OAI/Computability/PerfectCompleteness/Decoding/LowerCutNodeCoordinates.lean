import OAI.Computability.PerfectCompleteness.Decoding.LowerDirectionFiber
import OAI.Computability.PerfectCompleteness.Foundations.WholeArrayInteriorExteriorLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutNodeCoordinates

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

def scalarEquiv : {n m : Nat} → (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      H (subtreeSlots p slots) ≃ₗ[F2] H (nodeSlots slots (upperNode p))
  | _, _, .refl _, _ => LinearEquiv.refl F2 _
  | _, _, .step i p, slots => scalarEquiv p (childSlots slots i)

def rowIndexEquiv (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
      Fin (rows (m + 1)) ≃ Fin (rows (Nodes.height (upperNode p)))
  | _, _, .refl _ => Equiv.refl _
  | _, _, .step _ p => rowIndexEquiv rows p

def directionEquiv (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
      BucketSampler.Direction (rows (m + 1)) ≃
        BucketSampler.Direction (rows (Nodes.height (upperNode p)))
  | _, _, .refl _ => Equiv.refl _
  | _, _, .step _ p => directionEquiv rows p

def rowEquiv (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (Fin (rows (m + 1)) → H (subtreeSlots p slots)) ≃ₗ[F2]
        (Fin (rows (Nodes.height (upperNode p))) → H (nodeSlots slots (upperNode p)))
  | _, _, .refl _, _ => LinearEquiv.refl F2 _
  | _, _, .step i p, slots => rowEquiv rows p (childSlots slots i)

theorem directionEquiv_apply (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (a : BucketSampler.Direction (rows (m + 1))) → (i : Fin (rows (m + 1))) →
      (directionEquiv rows p a).val (rowIndexEquiv rows p i) = a.val i
  | _, _, .refl _, _, _ => rfl
  | _, _, .step _ p, a, i => directionEquiv_apply rows p a i

theorem rowEquiv_apply (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (S : Fin (rows (m + 1)) → H (subtreeSlots p slots)) →
      (i : Fin (rows (m + 1))) →
      rowEquiv rows p slots S (rowIndexEquiv rows p i) = scalarEquiv p slots (S i)
  | _, _, .refl _, _, _, _ => rfl
  | _, _, .step i p, slots, S, j => rowEquiv_apply rows p (childSlots slots i) S j

theorem pivot_transport (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (a : BucketSampler.Direction (rows (m + 1))) →
      rowIndexEquiv rows p (LowerDirectionFiber.pivot a) =
        LowerDirectionFiber.pivot (directionEquiv rows p a)
  | _, _, .refl _, _ => rfl
  | _, _, .step _ p, a => pivot_transport rows p a

theorem rowEquiv_selectedRows (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (arrays : Arrays slots rows) →
      rowEquiv rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays) =
        arrays (upperNode p)
  | _, _, .refl _, _, _ => rfl
  | _, _, .step i p, slots, arrays =>
      rowEquiv_selectedRows rows p (childSlots slots i) (fun node => arrays (.inr (i, node)))

theorem replace_eq_update (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots p slots)) :
    SelectedArrayReplacement.replace rows p slots arrays fresh =
      Function.update arrays (upperNode p) (rowEquiv rows p slots fresh) := by
  funext node
  by_cases hnode : node = upperNode p
  · subst node
    rw [Function.update_self]
    have h := rowEquiv_selectedRows rows p slots
      (SelectedArrayReplacement.replace rows p slots arrays fresh)
    rw [SelectedArrayReplacement.selectedRows_replace] at h
    exact h.symm
  · rw [Function.update_of_ne hnode]
    exact SelectedArrayReplacement.replace_outside rows p slots arrays fresh node hnode

theorem rowEquiv_replace (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (a : BucketSampler.Direction (rows (m + 1))) →
      (S : Fin (rows (m + 1)) → H (subtreeSlots p slots)) →
      (fresh : H (subtreeSlots p slots)) →
      rowEquiv rows p slots (LowerDirectionFiber.replace a S fresh) =
        LowerDirectionFiber.replace (directionEquiv rows p a)
          (rowEquiv rows p slots S) (scalarEquiv p slots fresh)
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .step i p, slots, a, S, fresh =>
      rowEquiv_replace rows p (childSlots slots i) a S fresh

theorem replace_fiber_eq_update (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (subtreeSlots p slots)) :
    SelectedArrayReplacement.replace rows p slots arrays
        (LowerDirectionFiber.replace a
          (SelectedArrayReplacement.selectedRows rows p slots arrays) fresh) =
      Function.update arrays (upperNode p)
        (LowerDirectionFiber.replace (directionEquiv rows p a)
          (arrays (upperNode p)) (scalarEquiv p slots fresh)) := by
  rw [replace_eq_update, rowEquiv_replace, rowEquiv_selectedRows]

end
end PerfectCompleteness.LowerCutNodeCoordinates

end

end OAI
