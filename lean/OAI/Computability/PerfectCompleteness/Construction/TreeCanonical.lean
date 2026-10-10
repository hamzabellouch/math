import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import OAI.Computability.PerfectCompleteness.Construction.TreeSourceSpaces
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalKeys

namespace OAI

section

namespace PerfectCompleteness.TreeCanonical

open MixedSupport TreeSourceSpaces

noncomputable section

abbrev Location (branch : Nat → Nat) (n t : Nat) := RecursiveSpaces.Slots branch n × Fin t

def locationCount (branch : Nat → Nat) (n t : Nat) : Nat :=
  Fintype.card (Location branch n t)

def numbering (branch : Nat → Nat) (n t : Nat) :
    Location branch n t ≃ Fin (locationCount branch n t) :=
  Fintype.equivFin (Location branch n t)

variable {branch : Nat → Nat} {n t : Nat} {Y : Type*}

def numberedSlots (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Fin (locationCount branch n t) → Slot :=
  fun j => flatSlots slots ((numbering branch n t).symm j)

def assignmentEquiv (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) :
    Domain slots ≃ MixedSupport.Assignment (numberedSlots slots) :=
  (flattenAssignment slots).trans
    (Equiv.piCongrLeft' (fun sk : Location branch n t => (flatSlots slots sk).Domain)
      (numbering branch n t))

@[simp] theorem assignmentEquiv_apply
    (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) (x : Domain slots)
    (j : Fin (locationCount branch n t)) :
    assignmentEquiv slots x j =
      x ((numbering branch n t).symm j).1 ((numbering branch n t).symm j).2 := rfl

def numberedProjection {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) :
    ∀ j, Projection (numberedSlots slots j) (numberedSlots projected j) :=
  fun j => p ((numbering branch n t).symm j).1 ((numbering branch n t).symm j).2

theorem assignmentEquiv_projection
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) (x : Domain slots) :
    assignmentEquiv projected (sourceProjection p x) =
      MixedSupport.projectionMap (numberedProjection p) (assignmentEquiv slots x) := rfl

theorem assignmentEquiv_symm_projection
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k))
    (x : MixedSupport.Assignment (numberedSlots slots)) :
    sourceProjection p ((assignmentEquiv slots).symm x) =
      (assignmentEquiv projected).symm (MixedSupport.projectionMap (numberedProjection p) x) := by
  apply (assignmentEquiv projected).injective
  simpa only [Equiv.apply_symm_apply] using
    assignmentEquiv_projection p ((assignmentEquiv slots).symm x)

def numberedFunction (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (f : Domain slots → Y) : MixedSupport.Assignment (numberedSlots slots) → Y :=
  f ∘ (assignmentEquiv slots).symm

theorem numberedFunction_projection
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) (f : Domain projected → Y) :
    numberedFunction slots (f ∘ sourceProjection p) =
      numberedFunction projected f ∘ MixedSupport.projectionMap (numberedProjection p) := by
  funext x
  exact congrArg f (assignmentEquiv_symm_projection p x)

def key (side : CanonicalKeys.Side)
    (slots : RecursiveSpaces.Slots branch n → Fin t → Slot) (f : Domain slots → Y) :
    CanonicalKeys.Key (locationCount branch n t) :=
  CanonicalKeys.key side (numberedSlots slots) (numberedFunction slots f)

theorem key_projection (side : CanonicalKeys.Side)
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) (f : Domain projected → Y) :
    key side slots (f ∘ sourceProjection p) = key side projected f := by
  unfold key
  rw [numberedFunction_projection]
  exact CanonicalKeys.key_projection side (numberedProjection p) (numberedFunction projected f)

theorem H_key_projection (side : CanonicalKeys.Side)
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) (f : H projected) :
    key side slots (HPullback p f).val = key side projected f.val :=
  key_projection side p f.val

abbrev Label (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (f : Domain slots → Y) :=
  CanonicalKeys.Label (numberedSlots slots) (numberedFunction slots f)

def evaluateLabel (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (f : Domain slots → Y) (x : Domain slots) : Label slots f :=
  CanonicalKeys.evaluateLabel (numberedSlots slots) (numberedFunction slots f)
    (assignmentEquiv slots x)

def restore (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (f : Domain slots → Y) (P : Label slots f) : Y :=
  CanonicalKeys.restore (numberedSlots slots) (numberedFunction slots f) P

@[simp] theorem restore_evaluateLabel
    (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (f : Domain slots → Y) (x : Domain slots) :
    restore slots f (evaluateLabel slots f x) = f x := by
  simpa only [restore, evaluateLabel, numberedFunction, Function.comp_apply,
    Equiv.symm_apply_apply] using
    CanonicalKeys.restore_evaluateLabel (numberedSlots slots) (numberedFunction slots f)
      (assignmentEquiv slots x)

theorem restore_injective (slots : RecursiveSpaces.Slots branch n → Fin t → Slot)
    (f : Domain slots → Y) : Function.Injective (restore slots f) :=
  CanonicalKeys.restore_injective (numberedSlots slots) (numberedFunction slots f)

end

end PerfectCompleteness.TreeCanonical

end

end OAI
