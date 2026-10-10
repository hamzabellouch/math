import OAI.Computability.PerfectCompleteness.Decoding.CleanDecoderOddLists
import OAI.Computability.PerfectCompleteness.Decoding.CleanEndpointProjection
import OAI.Computability.PerfectCompleteness.Machines.CleanRecordDecoderInput
import OAI.Computability.PerfectCompleteness.Repetition.CleanRecordObservation

namespace OAI

section

namespace PerfectCompleteness.CleanRecordProjection

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces

variable {branch : Nat → Nat} {h t v m : Nat} [NeZero m]
  {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

omit [NeZero m] in
private theorem sourceProjection_congr (b b' : Bool)
    (e e' : SourceOddLists.Occurrences m t) (hb : b = b') (he : e = e') (k : Fin t) :
    HEq (CleanEndpointProjection.sourceProjection clauses b e k)
      (CleanEndpointProjection.sourceProjection clauses b' e' k) := by
  cases hb
  cases he
  rfl

omit [NeZero m] in
private theorem sourceProjection_tree (i : Fin (branch h))
    (source : SourceChildKernel.Source (m := m) (t := t) designated i)
    (b : Bool) (leaf : Slots branch h) (k : Fin t) :
    HEq (CleanEndpointProjection.sourceProjection clauses b
      (SourceChildKernel.tree designated i source leaf) k)
      (SourceChildKernel.projection clauses designated i source b leaf k) := by
  cases b <;> rfl

omit [NeZero m] in
theorem insideProjection_heq
    (record : CleanRecordObservation.Record (C := C) (t := t) rows clauses designated)
    (x : CleanRecordObservation.Sample (C := C) (t := t) rows clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (s : Slots branch (h + 1)) (k : Fin t) :
    HEq
      (CleanEndpointProjection.insideProjection clauses designated
        (CleanRecordChildBlocks.clean rows clauses designated record)
        (CleanRecordChildBlocks.visible rows clauses designated record)
        (CleanRecordChildBlocks.projected rows clauses designated record)
        (CleanSourceRecord.clean_projected designated
          (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record)
        (fun i => (x i.val).1) s k)
      (SourceChildKernel.parentProjection rows clauses designated
        (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2) s k) := by
  have hp := congrFun (CleanSourceRecord.projected_eq_raw designated
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
    record x hevent) s.1
  have hflag : CleanSourceRecord.rawProjected designated
      (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      s.1 (x s.1).2.2 =
        SourceChildKernel.rawProjected rows clauses designated s.1 (x s.1).2.2 := by
    cases (x s.1).2.2 <;> rfl
  by_cases hs : CleanRecordChildBlocks.clean rows clauses designated record s.1 ∧
      s.2 = designated s.1
  · simp only [CleanEndpointProjection.insideProjection, dite_eq_left hs]
    apply (CutProjectionAssembly.castProjection_heq _ _ _).trans
    have he : (x s.1).1 = SourceChildKernel.tree designated s.1
        ((x s.1).1, (x s.1).2.1) s.2 := by
      rw [hs.2]
      exact (CleanSourceRecord.assemble_designated designated s.1 _ _).symm
    exact (sourceProjection_congr clauses _ _ _ _ (hp.trans hflag) he k).trans
      (sourceProjection_tree clauses designated s.1 ((x s.1).1, (x s.1).2.1)
        (SourceChildKernel.rawProjected rows clauses designated s.1 (x s.1).2.2) s.2 k)
  · simp only [CleanEndpointProjection.insideProjection, dite_eq_right hs]
    apply (CutProjectionAssembly.castProjection_heq _ _ _).trans
    have hv := CleanSourceRecord.visible_eq_reveal designated
      (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
      record x hevent
    have he : CleanRecordChildBlocks.visible rows clauses designated record s.1 ⟨s.2, hs⟩ =
        SourceChildKernel.tree designated s.1 ((x s.1).1, (x s.1).2.1) s.2 :=
      congrArg (fun visible => visible s.1 ⟨s.2, hs⟩) hv
    exact (sourceProjection_congr clauses _ _ _ _ (hp.trans hflag) he k).trans
      (sourceProjection_tree clauses designated s.1 ((x s.1).1, (x s.1).2.1)
        (SourceChildKernel.rawProjected rows clauses designated s.1 (x s.1).2.2) s.2 k)

private theorem fillProjection_congr {n : Nat} (p : Path branch n (h + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    {left left' right right' : Slots branch (h + 1) → Fin t → MixedSupport.Slot}
    (hl : left = left') (hr : right = right')
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (q' : ∀ s k, MixedSupport.Projection (left' s k) (right' s k))
    (hq : ∀ s k, HEq (q s k) (q' s k)) (s : Slots branch n) (k : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q s k)
      (CutProjectionAssembly.fillProjection p outside left' right' q' s k) := by
  cases hl
  cases hr
  have hqq : q = q' := funext (fun s => funext (fun k => eq_of_heq (hq s k)))
  cases hqq
  rfl

omit [NeZero m] in
theorem fillProjection_heq {n : Nat} (p : Path branch n (h + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (record : CleanRecordObservation.Record (C := C) (t := t) rows clauses designated)
    (x : CleanRecordObservation.Sample (C := C) (t := t) rows clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (s : Slots branch n) (k : Fin t) :
    HEq
      (CutProjectionAssembly.fillProjection p outside _ _
        (CleanEndpointProjection.insideProjection clauses designated
          (CleanRecordChildBlocks.clean rows clauses designated record)
          (CleanRecordChildBlocks.visible rows clauses designated record)
          (CleanRecordChildBlocks.projected rows clauses designated record)
          (CleanSourceRecord.clean_projected designated
            (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record)
          (fun i => (x i.val).1)) s k)
      (CutProjectionAssembly.fillProjection p outside _ _
        (SourceChildKernel.parentProjection rows clauses designated
          (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)) s k) :=
  fillProjection_congr p outside
    (CleanRecordObservation.leftInside_eq rows clauses designated record x hevent)
    (CleanRecordObservation.rightInside_eq rows clauses designated record x hevent) _ _
    (insideProjection_heq rows clauses designated record x hevent) s k

theorem decoderProjection_heq {root : Nat} (repeats : Nat → Nat)
    (upper : HierarchicalArrays.Nodes branch root)
    (d : HierarchicalFrozenTables.LowerNodes upper (h + 1))
    (cut : OwnInputReference.Cut upper (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (record : CleanRecordDecoderInput.Record (t := t) rows repeats upper d cut clauses designated)
    (external : CleanRecordDecoderInput.Exterior rows repeats upper d cut outside placeholder)
    (x : CleanRecordDecoderInput.Sample (t := t) rows repeats upper d cut clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (s : Slots branch root) (k : Fin t) :
    HEq (CleanDecoderOddLists.fullProjection
      (CleanRecordDecoderInput.exposed rows repeats upper d cut outside placeholder
        clauses designated record external)
      (CleanRecordDecoderInput.sources rows repeats upper d cut clauses designated record x) s k)
      (CutProjectionAssembly.fillProjection (CleanRecordDecoderInput.path upper d cut) outside _ _
        (SourceChildKernel.parentProjection rows clauses designated
          (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)) s k) :=
  fillProjection_heq rows clauses designated (CleanRecordDecoderInput.path upper d cut)
    outside record x hevent s k

end
end PerfectCompleteness.CleanRecordProjection

end

end OAI
