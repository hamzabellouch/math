import OAI.Computability.PerfectCompleteness.Construction.ProjectedNodeEmbedding
import OAI.Computability.PerfectCompleteness.Decoding.RightDecoderLemmas
import OAI.Computability.PerfectCompleteness.Machines.LowerCutDecoderInput
import OAI.Computability.PerfectCompleteness.Machines.LowerCutOwnInput

namespace OAI

section

namespace PerfectCompleteness.ProjectedLowerFiber

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

abbrev lower := HierarchicalLeftDecoder.LowerNode upper level d
abbrev Scalar := H (nodeSlots projected (lower upper level d))
abbrev Direction := BucketSampler.Direction (rows (Nodes.height (lower upper level d)))

def arraysAt (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    Arrays projected rows :=
  Function.update arrays (lower upper level d)
    (LowerDirectionFiber.replace a (arrays (lower upper level d)) fresh)

theorem rightInput_fixed {r : Nat}
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d)
    (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
        (LinearMap.ker A) a.val known (arraysAt projected upper level d a arrays fresh) =
      LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
        (LinearMap.ker A) a.val known arrays :=
  LowerCutOwnInput.ofArrays_update projected rows upper (lower upper level d)
    (LinearMap.ker A) a known arrays fresh

theorem rightLaw_fixed {r : Nat}
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d)
    (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d)
    (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper (lower upper level d))
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (threshold : ℝ) :
    RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
        repeats cut σ
        (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
          (LinearMap.ker A) a.val known (arraysAt projected upper level d a arrays fresh)) threshold =
      RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
        repeats cut σ
        (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
          (LinearMap.ker A) a.val known arrays) threshold := by
  rw [rightInput_fixed projected upper level d A a known arrays fresh]

def originalArraysAt (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    Arrays slots rows :=
  ChildBlockProjection.arraysPullback rows projection
    (arraysAt projected upper level d a arrays fresh)

theorem originalArraysAt_eq_update
    (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    originalArraysAt slots projected projection upper level d a arrays fresh =
      Function.update (ChildBlockProjection.arraysPullback rows projection arrays)
        (lower upper level d)
        (fun i => HPullback (ChildBlockProjection.nodeProjection projection (lower upper level d))
          (LowerDirectionFiber.replace a (arrays (lower upper level d)) fresh i)) := by
  funext node
  by_cases hnode : node = lower upper level d
  · subst node
    funext i
    simp only [originalArraysAt, ChildBlockProjection.arraysPullback_apply,
      arraysAt, Function.update_self]
  · funext i
    simp only [originalArraysAt, ChildBlockProjection.arraysPullback_apply,
      arraysAt, Function.update_of_ne hnode]

def inputAt {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    HierarchicalAllDecoderTables.Input (rows := rows) slots upper level r :=
  LowerCutDecoderInput.actualInput slots upper level
    (originalArraysAt slots projected projection upper level d a arrays fresh) A

theorem inputAt_eq_lowerInput {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    inputAt slots projected projection upper level d A a arrays fresh =
      HierarchicalLowerMatrixInput.input slots upper level
        (HierarchicalMatrixTable.backgroundOf slots upper
          (ChildBlockProjection.arraysPullback rows projection arrays)) d
        (NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows projection arrays) upper) A
        (EvaluationMatrix.ofRows (HierarchicalDecoderTables.LowerH slots upper level d)
          (fun i => HPullback (ChildBlockProjection.nodeProjection projection (lower upper level d))
            (LowerDirectionFiber.replace a (arrays (lower upper level d)) fresh i))) := by
  unfold inputAt
  rw [originalArraysAt_eq_update]
  exact LowerCutDecoderInput.actualInput_update slots upper level
    (ChildBlockProjection.arraysPullback rows projection arrays) d A _

abbrev UpperTable (r : Nat) :=
  HierarchicalAllDecoderTables.Input (rows := rows) slots upper level r →
    HierarchicalAllDecoderTables.UpperAnswer slots upper

def upperAt {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d) (arrays : Arrays projected rows)
    (table : UpperTable (rows := rows) slots upper level r)
    (fresh : Scalar projected upper level d) :
    HierarchicalAllDecoderTables.UpperAnswer slots upper :=
  table (inputAt slots projected projection upper level d A a arrays fresh)

theorem upperTarget_eq_dualMap
    (q : HierarchicalAllDecoderTables.UpperAnswer slots upper) :
    DecoderSourcePullback.upperTarget projection upper q =
      (ProjectedNodeEmbedding.intoOriginal projection upper).dualMap q :=
  (ProjectedNodeEmbedding.dualMap_eq_upperTarget projection upper q).symm

end
end PerfectCompleteness.ProjectedLowerFiber

end

end OAI
