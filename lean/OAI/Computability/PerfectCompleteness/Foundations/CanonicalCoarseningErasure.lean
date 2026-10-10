import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Machines.CanonicalLabelEncoding

namespace OAI

section

namespace PerfectCompleteness.CanonicalCoarseningErasure

open MixedSupport CanonicalKeys CanonicalKeyShape CanonicalEdges

noncomputable section

variable {n : Nat} {Y Z : Type*}

def transportLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) : Label (dummySlots (shape slots)) (transport slots f) :=
  ⟨P.val, by
    change P.val ∈ CanonicalKeys.partition (dummySlots (shape slots)) (transport slots f)
    rw [← partition_erasure slots f]
    exact P.property⟩

@[simp] theorem transportLabel_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) : (transportLabel slots f P).val = P.val := rfl

theorem transportLabel_bijective (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Function.Bijective (transportLabel slots f) := by
  constructor
  · intro P Q h
    apply Subtype.ext
    exact congrArg
      (fun R : Label (dummySlots (shape slots)) (transport slots f) => R.val) h
  · intro Q
    have hQ : Q.val ∈ CanonicalKeys.partition slots f := by
      rw [partition_erasure slots f]
      exact Q.property
    exact ⟨⟨Q.val, hQ⟩, Subtype.ext rfl⟩

theorem transportLabel_evaluateLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (x : Assignment slots) :
    transportLabel slots f (evaluateLabel slots f x) =
      evaluateLabel (dummySlots (shape slots)) (transport slots f) (assignmentEquiv slots x) := by
  apply Subtype.ext
  exact ReducedPartition.fiber_eq_of_pullback
    (assignmentEquiv slots) (assignmentEquiv slots).surjective
    (reduction slots f) (reduction (dummySlots (shape slots)) (transport slots f))
    f (transport slots f) (reduction_erasure slots f)
    (fun x => (transport_apply slots f x).symm) x

theorem restore_transportLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) :
    restore slots f P =
      restore (dummySlots (shape slots)) (transport slots f) (transportLabel slots f P) := by
  exact ReducedPartition.output_eq_of_shared_part
    (assignmentEquiv slots)
    (reduction slots f) (reduction (dummySlots (shape slots)) (transport slots f))
    f (transport slots f) (reduction_erasure slots f)
    (fun x => (transport_apply slots f x).symm)
    (constantOnFibers (dummySlots (shape slots)) (transport slots f))
    P (transportLabel slots f P) rfl

theorem coarsen_transportLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    transportLabel slots (p ∘ f) (coarsen slots f p P) =
      coarsen (dummySlots (shape slots)) (transport slots f) p (transportLabel slots f P) := by
  apply restore_injective (dummySlots (shape slots)) (p ∘ transport slots f)
  calc
    restore (dummySlots (shape slots)) (p ∘ transport slots f)
        (transportLabel slots (p ∘ f) (coarsen slots f p P)) =
        restore slots (p ∘ f) (coarsen slots f p P) :=
      (restore_transportLabel slots (p ∘ f) (coarsen slots f p P)).symm
    _ = p (restore slots f P) := restore_coarsen slots f p P
    _ = p (restore (dummySlots (shape slots)) (transport slots f)
        (transportLabel slots f P)) := congrArg p (restore_transportLabel slots f P)
    _ = restore (dummySlots (shape slots)) (p ∘ transport slots f)
        (coarsen (dummySlots (shape slots)) (transport slots f) p (transportLabel slots f P)) :=
      (restore_coarsen (dummySlots (shape slots)) (transport slots f) p
        (transportLabel slots f P)).symm

theorem coarsen_val (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    (coarsen slots f p P).val =
      (coarsen (dummySlots (shape slots)) (transport slots f) p
        (transportLabel slots f P)).val :=
  congrArg Subtype.val (coarsen_transportLabel slots f p P)

@[simp] theorem partIndex_transportLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (transportLabel slots f P).val =
      CanonicalKeyEncoding.partEnum n P.val := rfl

theorem partIndex_coarsen (slots : Fin n → Slot) (f : Assignment slots → Y)
    (p : Y → Z) (P : Label slots f) :
    CanonicalKeyEncoding.partEnum n (coarsen slots f p P).val =
      CanonicalKeyEncoding.partEnum n
        (coarsen (dummySlots (shape slots)) (transport slots f) p
          (transportLabel slots f P)).val :=
  congrArg (CanonicalKeyEncoding.partEnum n) (coarsen_val slots f p P)

@[simp] theorem labelIndex_transportLabel (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (P : Label slots f) :
    CanonicalLabelEncoding.labelIndex (key side slots f) P =
      CanonicalLabelEncoding.labelIndex
        (key side (dummySlots (shape slots)) (transport slots f)) (transportLabel slots f P) := rfl

theorem labelIndex_coarsen (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) (p : Y → Z) (P : Label slots f) :
    CanonicalLabelEncoding.labelIndex (key side slots (p ∘ f)) (coarsen slots f p P) =
      CanonicalLabelEncoding.labelIndex
        (key side (dummySlots (shape slots)) (p ∘ transport slots f))
        (coarsen (dummySlots (shape slots)) (transport slots f) p
          (transportLabel slots f P)) :=
  partIndex_coarsen slots f p P

end
end PerfectCompleteness.CanonicalCoarseningErasure

end

end OAI
