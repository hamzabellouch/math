import Mathlib.Algebra.Field.ZMod
import OAI.Computability.PerfectCompleteness.Foundations.ClauseSupportLemmas
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaces

namespace OAI

section

namespace PerfectCompleteness.TreeSourceSpaces

open MixedSupport

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n t : Nat}

instance slotDomainFintype (s : Slot) : Fintype s.Domain := by
  cases s with
  | clause occurrence variableIDs signs =>
      exact inferInstanceAs (Fintype (ClauseSupport.Answer signs))
  | bit variableID => exact inferInstanceAs (Fintype Bool)

abbrev LeafDomain (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (s : RecursiveSpaces.Slots branch n) := MixedSupport.Assignment (slots s)

abbrev Domain (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :=
  RecursiveSpaces.Assignment (LeafDomain slots)

abbrev H (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Submodule F2 (Domain slots → F2) :=
  RecursiveSpaces.space F2 branch n (LeafDomain slots)

theorem domain_nonempty (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Nonempty (Domain slots) := by
  infer_instance

theorem domain_finite (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Finite (Domain slots) := by
  infer_instance

theorem H_finite (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Finite (H slots) := by
  infer_instance

theorem one_mem_H (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (hbranch : ∀ k < n, 0 < branch k) : (1 : Domain slots → F2) ∈ H slots :=
  RecursiveSpaces.one_mem_space branch n (LeafDomain slots) hbranch

theorem H_le_squareSpace (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (hbranch : ∀ k < n, 0 < branch k) : H slots ≤ PointwiseSpaces.squareSpace (H slots) :=
  RecursiveSpaces.space_le_squareSpace (LeafDomain slots) hbranch

theorem one_mem_squareSpace (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (hbranch : ∀ k < n, 0 < branch k) :
    (1 : Domain slots → F2) ∈ PointwiseSpaces.squareSpace (H slots) :=
  RecursiveSpaces.one_mem_space_square (LeafDomain slots) hbranch

def sourceProjection {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    Domain slots → Domain projected :=
  RecursiveSpaces.project (fun s => MixedSupport.projectionMap (p s))

@[simp] theorem sourceProjection_apply
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k))
    (x : Domain slots) (s : RecursiveSpaces.Slots branch n) (k : Fin t) :
    sourceProjection p x s k = (p s k).map (x s k) := rfl

theorem sourceProjection_surjective
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    Function.Surjective (sourceProjection p) :=
  RecursiveSpaces.project_surjective _
    (fun s => MixedSupport.projectionMap_surjective (p s))

theorem H_pullback_le {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    (H projected).map (PointwiseSpaces.pullback F2 (sourceProjection p)) ≤ H slots :=
  RecursiveSpaces.space_project_le branch n (LeafDomain slots) (LeafDomain projected)
    (fun s => MixedSupport.projectionMap (p s))

theorem squareSpace_pullback_le
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    (PointwiseSpaces.squareSpace (H projected)).map
        (PointwiseSpaces.pullback F2 (sourceProjection p)) ≤
      PointwiseSpaces.squareSpace (H slots) :=
  PointwiseSpaces.squareSpace_pullback_le _ _ _ (H_pullback_le p)

def HPullback {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) : H projected →ₗ[F2] H slots :=
  RecursiveSpaces.spacePullback (LeafDomain slots) (LeafDomain projected)
    (fun s => MixedSupport.projectionMap (p s))

@[simp] theorem HPullback_apply
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k))
    (f : H projected) (x : Domain slots) :
    (HPullback p f).val x = f.val (sourceProjection p x) := rfl

theorem HPullback_injective
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    Function.Injective (HPullback p) :=
  RecursiveSpaces.spacePullback_injective (LeafDomain slots) (LeafDomain projected)
    (fun s => MixedSupport.projectionMap (p s))
    (fun s => MixedSupport.projectionMap_surjective (p s))

abbrev childSlots (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) : RecursiveSpaces.Slots branch n → Fin t → Slot :=
  fun s => slots (i, s)

def restrictChild (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) : Domain slots → Domain (childSlots slots i) :=
  RecursiveSpaces.childRestriction (LeafDomain slots) i

theorem child_square_le_H (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) :
    (PointwiseSpaces.squareSpace (H (childSlots slots i))).map
        (PointwiseSpaces.pullback F2 (restrictChild slots i)) ≤ H slots :=
  RecursiveSpaces.child_square_le_space (LeafDomain slots) i

theorem child_H_le_H (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) (hbranch : ∀ k < n, 0 < branch k) :
    (H (childSlots slots i)).map (PointwiseSpaces.pullback F2 (restrictChild slots i)) ≤ H slots :=
  RecursiveSpaces.child_le_space (LeafDomain slots) i hbranch

theorem restrictChild_surjective (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → Slot)
    (i : Fin (branch n)) : Function.Surjective (restrictChild slots i) :=
  RecursiveSpaces.childRestriction_surjective (LeafDomain slots) (fun _ => inferInstance) i

def flatSlots (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    RecursiveSpaces.Slots branch n × Fin t → Slot := fun sk => slots sk.1 sk.2

def flattenAssignment (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Domain slots ≃ MixedSupport.Assignment (flatSlots slots) where
  toFun x sk := x sk.1 sk.2
  invFun x s k := x (s, k)
  left_inv x := by
    funext s k
    rfl
  right_inv x := by
    funext sk
    cases sk
    rfl

theorem flattenAssignment_projection
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) (x : Domain slots) :
    flattenAssignment projected (sourceProjection p x) =
      MixedSupport.projectionMap
        (fun sk : RecursiveSpaces.Slots branch n × Fin t => p sk.1 sk.2)
        (flattenAssignment slots x) := rfl

end PerfectCompleteness.TreeSourceSpaces

end

end OAI
