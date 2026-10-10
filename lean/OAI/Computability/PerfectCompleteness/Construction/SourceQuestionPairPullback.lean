import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionPhysicalHigh
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutFiberDisintegrationLemmas
import OAI.Computability.PerfectCompleteness.Decoding.WholeCutGroupedProjection

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPairPullback

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior

variable {branch : Nat → Nat} {n height t : Nat}

def rawAtCut (rows repeats : Nat → Nat) (path : Path branch n (height + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (inside : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) inside rows) :
    LowerCutPair.Raw rows repeats path (CutSlotAssembly.fill path outside inside) :=
  SourceQuestionLowerForms.rawCast rows
    (CleanPhysicalReplay.cutSlots_fill path outside inside).symm raw

theorem selectedRows_pullback (rows : Nat → Nat) :
    {n height : Nat} → (path : Path branch n (height + 1)) →
      (left right : Slots branch n → Fin t → MixedSupport.Slot) →
      (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j)) →
      (arrays : Arrays right rows) →
      SelectedArrayReplacement.selectedRows rows path left
          (ChildBlockProjection.arraysPullback rows p arrays) =
        (fun i => HPullback (CutGroupedProjection.cutProjection path p)
          (SelectedArrayReplacement.selectedRows rows path right arrays i))
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .step child path, left, right, p, arrays =>
      selectedRows_pullback rows path (childSlots left child) (childSlots right child)
        (fun leaf j => p (child, leaf) j) (fun node => arrays (.inr (child, node)))

section Grouped

variable (rows repeats : Nat → Nat) (path : Path branch n (height + 1))
  (left right : Slots branch n → Fin t → MixedSupport.Slot)
  (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j))
  (hs : ∀ leaf, WholeCutExteriorTransport.Outside path leaf → left leaf = right leaf)
  (hk : ∀ leaf, WholeCutExteriorTransport.Outside path leaf → ∀ j,
    HEq (p leaf j) (MixedSupport.Projection.keep (left leaf j)))
  (exterior : WholeCutGrouping.Exterior rows repeats path right)

include hk in

theorem first_grouped_pullback (raw : LowerCutPair.Raw rows repeats path right) :
    ChildBlockProjection.arraysPullback rows p
        (LowerCutPair.first rows repeats path right exterior raw) =
      LowerCutPair.first rows repeats path left
        (WholeCutExteriorTransport.equiv rows repeats path right left
          (fun leaf h => (hs leaf h).symm) exterior)
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw) := by
  symm
  change WholeCutGroupedProjection.evaluateGrouped rows repeats path left _
      (CutCallExtension.original (WholeCutGrouping.cutSlots path left) rows
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw)) =
    ChildBlockProjection.arraysPullback rows p
      (WholeCutGroupedProjection.evaluateGrouped rows repeats path right exterior
        (CutCallExtension.original (WholeCutGrouping.cutSlots path right) rows raw))
  rw [LowerCutProjection.original_pullback]
  exact WholeCutGroupedProjection.evaluateGrouped_pullback rows repeats path
    left right p hs hk exterior _

include hk in

theorem second_grouped_pullback
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : LowerCutPair.Raw rows repeats path right) :
    ChildBlockProjection.arraysPullback rows p
        (LowerCutPair.second rows repeats path right exterior direction raw) =
      LowerCutPair.second rows repeats path left
        (WholeCutExteriorTransport.equiv rows repeats path right left
          (fun leaf h => (hs leaf h).symm) exterior) direction
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw) := by
  let exterior' := WholeCutExteriorTransport.equiv rows repeats path right left
    (fun leaf h => (hs leaf h).symm) exterior
  have hselected :
      SelectedArrayReplacement.selectedRows rows path left
          (ChildBlockProjection.arraysPullback rows p
            (LowerCutPair.second rows repeats path right exterior direction raw)) =
        SelectedArrayReplacement.selectedRows rows path left
          (LowerCutPair.second rows repeats path left exterior' direction
            (ChildAssemblyProjection.rawPullback rows
              (CutGroupedProjection.cutProjection path p) raw)) := by
    rw [selectedRows_pullback]
    exact (congrArg Prod.snd
      (LowerCutProjection.selectedPair_pullback rows repeats path
        (CutGroupedProjection.cutProjection path p) exterior' exterior direction raw)).symm
  funext node
  by_cases hnode : node = upperNode path
  · subst node
    simpa only [LowerCutNodeCoordinates.rowEquiv_selectedRows] using
      congrArg (LowerCutNodeCoordinates.rowEquiv rows path left) hselected
  · funext row
    change HPullback (ChildBlockProjection.nodeProjection p node)
        (LowerCutPair.second rows repeats path right exterior direction raw node row) =
      LowerCutPair.second rows repeats path left exterior' direction
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw) node row
    rw [LowerCutPair.second_outside rows repeats path right exterior direction raw node hnode,
      LowerCutPair.second_outside rows repeats path left exterior' direction _ node hnode]
    exact congrFun (congrFun
      (first_grouped_pullback rows repeats path left right p hs hk exterior raw) node) row

end Grouped

section Filled

private theorem rawCast_child_heq {C : Type*} [Fintype C] (rows : Nat → Nat)
    {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}
    (h : source = target) (raw : CutChildGrouping.Raw (C := C) source rows)
    (i : Fin (branch height)) :
    HEq ((SourceQuestionLowerForms.rawCast rows h raw) i) (raw i) := by
  cases h
  rfl

theorem rawAtCut_pullback (rows repeats : Nat → Nat)
    (path : Path branch n (height + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
    (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j))
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) right rows) :
    rawAtCut rows repeats path outside left
        (ChildAssemblyProjection.rawPullback rows p raw) =
      ChildAssemblyProjection.rawPullback rows
        (CutGroupedProjection.cutProjection path
          (CutProjectionAssembly.fillProjection path outside left right p))
        (rawAtCut rows repeats path outside right raw) := by
  funext i
  apply eq_of_heq
  exact (rawCast_child_heq rows
      (CleanPhysicalReplay.cutSlots_fill path outside left).symm
      (ChildAssemblyProjection.rawPullback rows p raw) i).trans
    (CutProjectionGeometry.childPullback_heq rows
      (CleanPhysicalReplay.cutSlots_fill path outside left)
      (CleanPhysicalReplay.cutSlots_fill path outside right)
      (CutGroupedProjection.cutProjection path
        (CutProjectionAssembly.fillProjection path outside left right p)) p
      (CutProjectionAssembly.fillProjection_at_cut path outside left right p) i
      (rawAtCut rows repeats path outside right raw i) (raw i)
      (rawCast_child_heq rows
        (CleanPhysicalReplay.cutSlots_fill path outside right).symm raw i)).symm

variable (rows repeats : Nat → Nat) (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder left right : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j))
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)

theorem first_pullback
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) right rows) :
    ChildBlockProjection.arraysPullback rows
        (CutProjectionAssembly.fillProjection path outside left right p)
        (LowerCutPair.first rows repeats path (CutSlotAssembly.fill path outside right)
          (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior)
          (rawAtCut rows repeats path outside right raw)) =
      LowerCutPair.first rows repeats path (CutSlotAssembly.fill path outside left)
        (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder left exterior)
        (rawAtCut rows repeats path outside left
          (ChildAssemblyProjection.rawPullback rows p raw)) := by
  rw [rawAtCut_pullback,
    WholeCutGroupedProjection.exteriorAt_pullback rows repeats path outside placeholder
      left right exterior]
  exact first_grouped_pullback rows repeats path
    (CutSlotAssembly.fill path outside left) (CutSlotAssembly.fill path outside right)
    (CutProjectionAssembly.fillProjection path outside left right p)
    (CutSlotAssembly.fill_outside_eq path outside left right)
    (CutProjectionGeometry.fillProjection_outside path outside left right p)
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior) _

theorem second_pullback
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) right rows) :
    ChildBlockProjection.arraysPullback rows
        (CutProjectionAssembly.fillProjection path outside left right p)
        (LowerCutPair.second rows repeats path (CutSlotAssembly.fill path outside right)
          (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior)
          direction (rawAtCut rows repeats path outside right raw)) =
      LowerCutPair.second rows repeats path (CutSlotAssembly.fill path outside left)
        (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder left exterior)
        direction (rawAtCut rows repeats path outside left
          (ChildAssemblyProjection.rawPullback rows p raw)) := by
  rw [rawAtCut_pullback,
    WholeCutGroupedProjection.exteriorAt_pullback rows repeats path outside placeholder
      left right exterior]
  exact second_grouped_pullback rows repeats path
    (CutSlotAssembly.fill path outside left) (CutSlotAssembly.fill path outside right)
    (CutProjectionAssembly.fillProjection path outside left right p)
    (CutSlotAssembly.fill_outside_eq path outside left right)
    (CutProjectionGeometry.fillProjection_outside path outside left right p)
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior)
    direction _

end Filled
end
end PerfectCompleteness.SourceQuestionPairPullback

end

end OAI
