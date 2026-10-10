import OAI.Computability.PerfectCompleteness.Foundations.SourcePhysicalExteriorSwap
import OAI.Computability.PerfectCompleteness.Machines.SourcePhysicalTapeLaw

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalExteriorReplay

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))

private theorem splitTape_symm_heq
    {slots target : Slots branch root → Fin t → MixedSupport.Slot}
    (hslots : slots = target)
    (external : WholeCutGrouping.Exterior rows repeats p slots)
    (other : WholeCutGrouping.Exterior rows repeats p target)
    (hext : HEq external other)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p slots) rows)
    (otherChildren : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p target) rows)
    (hchildren : ∀ child, HEq (children child) (otherChildren child)) :
    HEq ((WholeCutGrouping.splitTape rows repeats p slots).symm (external, children))
      ((WholeCutGrouping.splitTape rows repeats p target).symm (other, otherChildren)) := by
  cases hslots
  have he : external = other := eq_of_heq hext
  have hc : children = otherChildren := funext (fun child => eq_of_heq (hchildren child))
  cases he
  cases hc
  rfl

theorem physicalTape_heq
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder otherPlaceholder inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (hfill : CutSlotAssembly.fill p outside inside = CutSlotAssembly.fill p otherOutside inside)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (other : CleanPhysicalReplay.Exterior rows repeats p otherOutside otherPlaceholder)
    (hext : HEq external other)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    HEq (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children)
      (CleanPhysicalReplay.physicalTape rows repeats p otherOutside otherPlaceholder inside other children) := by
  apply splitTape_symm_heq rows repeats p hfill
  · exact (cast_heq _ _).trans (hext.trans (cast_heq _ _).symm)
  · intro child
    exact (CleanPhysicalReplay.fillChild_heq rows repeats p outside inside child (children child)).trans
      (CleanPhysicalReplay.fillChild_heq rows repeats p otherOutside inside child (children child)).symm

private theorem collapse_heq
    {slots target : Slots branch root → Fin t → MixedSupport.Slot}
    (hslots : slots = target)
    (tape : WholeCutSampler.Tape rows repeats p slots)
    (other : WholeCutSampler.Tape rows repeats p target) (htape : HEq tape other) :
    HEq (WholeCutSampler.collapse rows repeats p slots tape)
      (WholeCutSampler.collapse rows repeats p target other) := by
  cases hslots
  cases htape
  rfl

private theorem evaluate_heq
    {slots target : Slots branch root → Fin t → MixedSupport.Slot}
    (hslots : slots = target)
    (tape : WholeCutSampler.Tape rows repeats p slots)
    (other : WholeCutSampler.Tape rows repeats p target) (htape : HEq tape other) :
    HEq (WholeCutSampler.evaluate rows repeats p slots tape)
      (WholeCutSampler.evaluate rows repeats p target other) := by
  cases hslots
  cases htape
  rfl

theorem collapsedTape_heq
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder otherPlaceholder inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (hfill : CutSlotAssembly.fill p outside inside = CutSlotAssembly.fill p otherOutside inside)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (other : CleanPhysicalReplay.Exterior rows repeats p otherOutside otherPlaceholder)
    (hext : HEq external other)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    HEq (WholeCutSampler.collapse rows repeats p (CutSlotAssembly.fill p outside inside)
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children))
      (WholeCutSampler.collapse rows repeats p (CutSlotAssembly.fill p otherOutside inside)
        (CleanPhysicalReplay.physicalTape rows repeats p otherOutside otherPlaceholder inside other children)) :=
  collapse_heq rows repeats p hfill _ _
    (physicalTape_heq rows repeats p outside otherOutside placeholder otherPlaceholder inside
      hfill external other hext children)

theorem arrays_heq
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder otherPlaceholder inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (hfill : CutSlotAssembly.fill p outside inside = CutSlotAssembly.fill p otherOutside inside)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (other : CleanPhysicalReplay.Exterior rows repeats p otherOutside otherPlaceholder)
    (hext : HEq external other)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    HEq (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside inside)
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children))
      (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p otherOutside inside)
        (CleanPhysicalReplay.physicalTape rows repeats p otherOutside otherPlaceholder inside other children)) :=
  evaluate_heq rows repeats p hfill _ _
    (physicalTape_heq rows repeats p outside otherOutside placeholder otherPlaceholder inside
      hfill external other hext children)

end
end PerfectCompleteness.SourcePhysicalExteriorReplay

end

end OAI
