import OAI.Computability.PerfectCompleteness.Decoding.LowerCutFiberDisintegrationLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedFiberRawPair

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberBackground

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}

def nodeScalarEquiv
    (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node') :
    H (nodeSlots projected node) ≃ₗ[F2] H (nodeSlots projected node') := by
  cases h
  exact LinearEquiv.refl F2 _

@[simp] theorem nodeScalarEquiv_apply
    (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node')
    (x : H (nodeSlots projected node)) :
    nodeScalarEquiv projected h x = ProjectedFiberRawPair.castScalar projected h x := by
  cases h
  rfl

private theorem update_fiber_transport (rows : Nat → Nat)
    (projected : Slots branch n → Fin t → MixedSupport.Slot)
    {node node' : Nodes branch n} (h : node = node')
    (a : BucketSampler.Direction (rows (Nodes.height node)))
    (arrays : Arrays projected rows) (fresh : H (nodeSlots projected node)) :
    Function.update arrays node (LowerDirectionFiber.replace a (arrays node) fresh) =
      Function.update arrays node'
        (LowerDirectionFiber.replace (ProjectedFiberRawPair.castDirection h a) (arrays node')
          (ProjectedFiberRawPair.castScalar projected h fresh)) := by
  cases h
  rfl

variable (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  (projected : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : upperNode path = HierarchicalLeftDecoder.LowerNode upper level d)

def scalarEquiv : H (WholeCutGrouping.cutSlots path projected) ≃ₗ[F2]
    ProjectedLowerFiber.Scalar projected upper level d :=
  (LowerCutNodeCoordinates.scalarEquiv path projected).trans
    (nodeScalarEquiv projected hnode)

@[simp] theorem scalarEquiv_apply (x : H (WholeCutGrouping.cutSlots path projected)) :
    scalarEquiv path projected upper level d hnode x =
      ProjectedFiberRawPair.scalar path projected upper level d hnode x := by
  exact nodeScalarEquiv_apply projected hnode
    (LowerCutNodeCoordinates.scalarEquiv path projected x)

theorem scalar_uniform :
    (FiniteDistribution.uniform (H (WholeCutGrouping.cutSlots path projected))).pushforward
        (ProjectedFiberRawPair.scalar path projected upper level d hnode) =
      FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d) := by
  have h := UniformConditioning.uniform_transport
    (scalarEquiv path projected upper level d hnode).toEquiv
  rw [FiniteDistribution.transport_eq_pushforward] at h
  have hmap : ProjectedFiberRawPair.scalar path projected upper level d hnode =
      (scalarEquiv path projected upper level d hnode).toEquiv := by
    funext x
    exact (scalarEquiv_apply path projected upper level d hnode x).symm
  rw [hmap]
  exact h

private theorem replace_replace (arrays : Arrays projected rows)
    (S T : Fin (rows (m + 1)) → H (WholeCutGrouping.cutSlots path projected)) :
    SelectedArrayReplacement.replace rows path projected
        (SelectedArrayReplacement.replace rows path projected arrays S) T =
      SelectedArrayReplacement.replace rows path projected arrays T := by
  simp only [LowerCutNodeCoordinates.replace_eq_update]
  funext node
  by_cases hnode : node = upperNode path
  · subst node
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hnode]

variable (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : WholeCutGrouping.Exterior rows repeats path projected)
  (background : LowerCutFiberDisintegration.Background rows repeats path projected a)

theorem arraysAt_eq_native_replace (fresh : H (WholeCutGrouping.cutSlots path projected)) :
    LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background fresh =
      SelectedArrayReplacement.replace rows path projected
        (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background 0)
        (LowerDirectionFiber.replace a
          (SelectedArrayReplacement.selectedRows rows path projected
            (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background 0))
          fresh) := by
  simp only [LowerCutFiberDisintegration.arraysAt, LowerCutPairBackground.installRows,
    SelectedArrayReplacement.selectedRows_replace, LowerDirectionFiber.replace,
    LowerDirectionFiber.complement_restore, replace_replace]

theorem arraysAt_eq_fiber (fresh : H (WholeCutGrouping.cutSlots path projected)) :
    LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background fresh =
      ProjectedLowerFiber.arraysAt projected upper level d
        (ProjectedFiberRawPair.direction path upper level d hnode a)
        (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background 0)
        (ProjectedFiberRawPair.scalar path projected upper level d hnode fresh) := by
  rw [arraysAt_eq_native_replace rows repeats path projected a exterior background fresh,
    LowerCutNodeCoordinates.replace_fiber_eq_update]
  exact update_fiber_transport rows projected hnode
    (LowerCutNodeCoordinates.directionEquiv rows path a)
    (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background 0)
    (LowerCutNodeCoordinates.scalarEquiv path projected fresh)

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))

theorem pullback_arraysAt (fresh : H (WholeCutGrouping.cutSlots path projected)) :
    ChildBlockProjection.arraysPullback rows projection
        (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background fresh) =
      ProjectedLowerFiber.originalArraysAt slots projected projection upper level d
        (ProjectedFiberRawPair.direction path upper level d hnode a)
        (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background 0)
        (ProjectedFiberRawPair.scalar path projected upper level d hnode fresh) :=
  congrArg (ChildBlockProjection.arraysPullback rows projection)
    (arraysAt_eq_fiber rows repeats path projected upper level d hnode a exterior background fresh)

variable (hbranch : ∀ k < n, 0 < branch k) {r : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) r)
  (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r)
  (s : Nat)

theorem form_at_fiber (fresh : H (WholeCutGrouping.cutSlots path projected)) :
    ProjectedFiberSquare.form slots upper level hbranch d s
        (ProjectedLowerFiber.upperAt slots projected projection upper level d A
          (ProjectedFiberRawPair.direction path upper level d hnode a)
          (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background 0)
          table (ProjectedFiberRawPair.scalar path projected upper level d hnode fresh)) =
      (LowerCutDecoderForm.answer slots upper level d hbranch A table s
        (ChildBlockProjection.arraysPullback rows projection
          (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior background fresh))).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)) := by
  rw [ProjectedFiberRawPair.form_upperAt,
    ← pullback_arraysAt rows repeats path projected upper level d hnode a exterior background
      slots projection fresh]

end
end PerfectCompleteness.ProjectedFiberBackground

end

end OAI
