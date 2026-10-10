import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedFiberSquare

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberRawPair

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior

variable {branch rows repeats : Nat → Nat} {n m t : Nat}

def castDirection {node node' : Nodes branch n} (h : node = node')
    (a : BucketSampler.Direction (rows (Nodes.height node))) :
    BucketSampler.Direction (rows (Nodes.height node')) := by
  cases h
  exact a

def castScalar (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node')
    (x : H (nodeSlots projected node)) : H (nodeSlots projected node') := by
  cases h
  exact x

private theorem castScalar_pivot
    (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node')
    (a : BucketSampler.Direction (rows (Nodes.height node)))
    (arrays : Arrays projected rows) :
    castScalar projected h (arrays node (LowerDirectionFiber.pivot a)) =
      arrays node' (LowerDirectionFiber.pivot (castDirection h a)) := by
  cases h
  rfl

private theorem update_fiber_transport
    (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node')
    (a : BucketSampler.Direction (rows (Nodes.height node)))
    (arrays : Arrays projected rows) (fresh : H (nodeSlots projected node)) :
    Function.update arrays node (LowerDirectionFiber.replace a (arrays node) fresh) =
      Function.update arrays node'
        (LowerDirectionFiber.replace (castDirection h a) (arrays node')
          (castScalar projected h fresh)) := by
  cases h
  rfl

variable (path : Path branch n (m + 1))
  (projected : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : upperNode path = HierarchicalLeftDecoder.LowerNode upper level d)

def direction (a : BucketSampler.Direction (rows (m + 1))) :
    ProjectedLowerFiber.Direction (rows := rows) upper level d :=
  castDirection hnode (LowerCutNodeCoordinates.directionEquiv rows path a)

def scalar (x : H (WholeCutGrouping.cutSlots path projected)) :
    ProjectedLowerFiber.Scalar projected upper level d :=
  castScalar projected hnode (LowerCutNodeCoordinates.scalarEquiv path projected x)

variable (exterior : WholeCutGrouping.Exterior rows repeats path projected)
  (a : BucketSampler.Direction (rows (m + 1)))
  (raw : LowerCutPair.Raw rows repeats path projected)

def oldScalar : ProjectedLowerFiber.Scalar projected upper level d :=
  scalar path projected upper level d hnode
    (SelectedArrayReplacement.selectedRows rows path projected
      (LowerCutPair.first rows repeats path projected exterior raw)
      (LowerDirectionFiber.pivot a))

def freshScalar : ProjectedLowerFiber.Scalar projected upper level d :=
  scalar path projected upper level d hnode
    (LowerCutPair.fresh rows repeats path projected raw)

theorem oldScalar_eq_pivot :
    oldScalar path projected upper level d hnode exterior a raw =
      LowerCutPair.first rows repeats path projected exterior raw
        (HierarchicalLeftDecoder.LowerNode upper level d)
        (LowerDirectionFiber.pivot (direction path upper level d hnode a)) := by
  have h := LowerCutNodeCoordinates.rowEquiv_apply rows path projected
    (SelectedArrayReplacement.selectedRows rows path projected
      (LowerCutPair.first rows repeats path projected exterior raw))
    (LowerDirectionFiber.pivot a)
  rw [LowerCutNodeCoordinates.rowEquiv_selectedRows,
    LowerCutNodeCoordinates.pivot_transport] at h
  unfold oldScalar scalar
  rw [← h]
  exact castScalar_pivot projected hnode
    (LowerCutNodeCoordinates.directionEquiv rows path a)
    (LowerCutPair.first rows repeats path projected exterior raw)

theorem first_eq_arraysAt :
    LowerCutPair.first rows repeats path projected exterior raw =
      ProjectedLowerFiber.arraysAt projected upper level d
        (direction path upper level d hnode a)
        (LowerCutPair.first rows repeats path projected exterior raw)
        (oldScalar path projected upper level d hnode exterior a raw) := by
  rw [oldScalar_eq_pivot]
  simp only [ProjectedLowerFiber.arraysAt, LowerDirectionFiber.replace,
    LowerDirectionFiber.restore_complement, Function.update_eq_self]

theorem second_eq_arraysAt :
    LowerCutPair.second rows repeats path projected exterior a raw =
      ProjectedLowerFiber.arraysAt projected upper level d
        (direction path upper level d hnode a)
        (LowerCutPair.first rows repeats path projected exterior raw)
        (freshScalar path projected upper level d hnode raw) := by
  rw [LowerCutOwnInput.second_eq_update]
  exact update_fiber_transport projected hnode
    (LowerCutNodeCoordinates.directionEquiv rows path a)
    (LowerCutPair.first rows repeats path projected exterior raw)
    (LowerCutNodeCoordinates.scalarEquiv path projected
      (LowerCutPair.fresh rows repeats path projected raw))

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))

theorem first_pullback :
    ChildBlockProjection.arraysPullback rows projection
        (LowerCutPair.first rows repeats path projected exterior raw) =
      ProjectedLowerFiber.originalArraysAt slots projected projection upper level d
        (direction path upper level d hnode a)
        (LowerCutPair.first rows repeats path projected exterior raw)
        (oldScalar path projected upper level d hnode exterior a raw) :=
  congrArg (ChildBlockProjection.arraysPullback rows projection)
    (first_eq_arraysAt path projected upper level d hnode exterior a raw)

theorem second_pullback :
    ChildBlockProjection.arraysPullback rows projection
        (LowerCutPair.second rows repeats path projected exterior a raw) =
      ProjectedLowerFiber.originalArraysAt slots projected projection upper level d
        (direction path upper level d hnode a)
        (LowerCutPair.first rows repeats path projected exterior raw)
        (freshScalar path projected upper level d hnode raw) :=
  congrArg (ChildBlockProjection.arraysPullback rows projection)
    (second_eq_arraysAt path projected upper level d hnode exterior a raw)

variable (hbranch : ∀ k < n, 0 < branch k) {r : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) r)
  (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r)
  (s : Nat)

theorem form_upperAt
    (dir : ProjectedLowerFiber.Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows)
    (fresh : ProjectedLowerFiber.Scalar projected upper level d) :
    ProjectedFiberSquare.form slots upper level hbranch d s
        (ProjectedLowerFiber.upperAt slots projected projection upper level d
          A dir arrays table fresh) =
      (LowerCutDecoderForm.answer slots upper level d hbranch A table s
        (ProjectedLowerFiber.originalArraysAt slots projected projection upper level d
          dir arrays fresh)).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)) := rfl

theorem first_form :
    ProjectedFiberSquare.form slots upper level hbranch d s
        (ProjectedLowerFiber.upperAt slots projected projection upper level d A
          (direction path upper level d hnode a)
          (LowerCutPair.first rows repeats path projected exterior raw) table
          (oldScalar path projected upper level d hnode exterior a raw)) =
      (LowerCutDecoderForm.answer slots upper level d hbranch A table s
        (ChildBlockProjection.arraysPullback rows projection
          (LowerCutPair.first rows repeats path projected exterior raw))).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)) := by
  rw [form_upperAt, ← first_pullback path projected upper level d hnode exterior a raw
    slots projection]

theorem second_form :
    ProjectedFiberSquare.form slots upper level hbranch d s
        (ProjectedLowerFiber.upperAt slots projected projection upper level d A
          (direction path upper level d hnode a)
          (LowerCutPair.first rows repeats path projected exterior raw) table
          (freshScalar path projected upper level d hnode raw)) =
      (LowerCutDecoderForm.answer slots upper level d hbranch A table s
        (ChildBlockProjection.arraysPullback rows projection
          (LowerCutPair.second rows repeats path projected exterior a raw))).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)) := by
  rw [form_upperAt, ← second_pullback path projected upper level d hnode exterior a raw
    slots projection]

end
end PerfectCompleteness.ProjectedFiberRawPair

end

end OAI
