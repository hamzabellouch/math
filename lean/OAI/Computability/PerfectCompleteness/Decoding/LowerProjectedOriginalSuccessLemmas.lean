import OAI.Computability.PerfectCompleteness.Decoding.LowerCutBucketLocality
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutFiberDisintegrationLemmas
import OAI.Computability.PerfectCompleteness.Decoding.LowerProjectedFiberAverage

namespace OAI

section

namespace PerfectCompleteness.LowerProjectedOriginalSuccess

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (path : Path branch n (m + 1))
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats path projected)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

def kernelSuccess (s : Nat)
    (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)
    (arrays : Arrays projected rows) : ℝ :=
  ((HierarchicalAllDecoderTables.upperKernel slots upper level σ useful r ρ
    (LowerCutDecoderInput.actualInput slots upper level
      (ChildBlockProjection.arraysPullback rows projection arrays) A)).product
    (RightDecoder.law projected rows upper (ProjectedLowerFiber.lower upper level d)
      (LinearMap.ker A) (ProjectedFiberRawPair.direction path upper level d hnode a).val
      repeats cut σ
      (LowerCutOwnInput.ofArrays projected rows upper (ProjectedLowerFiber.lower upper level d)
        (LinearMap.ker A) (ProjectedFiberRawPair.direction path upper level d hnode a).val
        known arrays) threshold)).probability
      (fun pair => ProjectedFiberSquare.highMeeting slots projected projection upper level hbranch d
        s pair.1 pair.2)

variable
  (known : LowerProjectedFiberAverage.Background path projected a →
    HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)

def rawSuccess (s : Nat) : ℝ :=
  (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats path)
    (cutSlots path projected) rows).expectation (fun raw =>
      kernelSuccess (repeats := repeats) path slots projected projection upper level hbranch d hnode a A cut σ useful
        ρ threshold s
        (known (LowerCutSingleFiberDisintegration.coordinates rows repeats path projected a raw).1)
        (LowerCutRows.reconstruct rows repeats path projected exterior raw))

theorem fiberSuccess_eq (s : Nat)
    (bg : LowerProjectedFiberAverage.Background path projected a) :
    ProjectedFiberSquare.success slots projected projection upper level hbranch d A
        (ProjectedFiberRawPair.direction path upper level d hnode a)
        (LowerProjectedFiberAverage.baseline path projected a exterior bg)
        (known bg) repeats cut σ useful ρ threshold s
        (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)) =
      (FiniteDistribution.uniform (H (cutSlots path projected))).expectation (fun fresh =>
        kernelSuccess (repeats := repeats) path slots projected projection upper level hbranch d hnode a A cut σ useful
          ρ threshold s (known bg)
          (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior bg fresh)) := by
  unfold ProjectedFiberSquare.success
  rw [← ProjectedFiberBackground.scalar_uniform path projected upper level d hnode,
    FiniteDistribution.expectation_pushforward]
  apply FiniteDistribution.expectation_congr
  intro fresh
  unfold ProjectedLowerFiber.inputAt ProjectedLowerFiber.originalArraysAt
    LowerProjectedFiberAverage.baseline kernelSuccess
  simp only [← ProjectedFiberBackground.arraysAt_eq_fiber rows repeats path projected upper level d hnode
    a exterior bg fresh]

theorem rawSuccess_eq_meanSuccess (s : Nat) :
    rawSuccess path slots projected projection upper level hbranch d hnode a exterior A cut σ useful
        ρ threshold known s =
      LowerProjectedFiberAverage.meanSuccess path slots projected projection upper level hbranch d hnode
        a exterior A known cut σ useful ρ threshold s := by
  have h := congrArg
    (fun μ : FiniteDistribution
        (LowerCutFiberDisintegration.Background rows repeats path projected a ×
          H (cutSlots path projected)) =>
      μ.expectation (fun z =>
        kernelSuccess (repeats := repeats) path slots projected projection upper level hbranch d hnode a A cut σ useful
          ρ threshold s (known z.1)
          (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior z.1 z.2)))
    (LowerCutSingleFiberDisintegration.coordinates_law rows repeats path projected a)
  rw [FiniteDistribution.expectation_pushforward, FiniteDistribution.expectation_product] at h
  simp only [← LowerCutSingleFiberDisintegration.reconstruct_eq_arraysAt
    rows repeats path projected a exterior] at h
  unfold rawSuccess LowerProjectedFiberAverage.meanSuccess
  refine h.trans ?_
  apply FiniteDistribution.expectation_congr
  intro bg
  exact (fiberSuccess_eq path slots projected projection upper level hbranch d hnode a exterior A cut σ
    useful ρ threshold known s bg).symm

theorem rawSuccess_square_le (s : Nat) :
    rawSuccess path slots projected projection upper level hbranch d hnode a exterior A cut σ useful
        ρ threshold known s ^ 2 ≤
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
        (LowerProjectedFiberAverage.rawCollision path slots projected projection upper level hbranch d
          a exterior A s) := by
  rw [rawSuccess_eq_meanSuccess]
  exact LowerProjectedFiberAverage.meanSuccess_square_le path slots projected projection upper level hbranch
    d hnode a exterior A known cut σ useful ρ threshold s

end
end PerfectCompleteness.LowerProjectedOriginalSuccess

end

section

namespace PerfectCompleteness.LowerPhysicalFiberSuccess

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n)
  (pDown : Path branch (Nodes.height upper) (m + 1))
  (hproper : m + 1 < Nodes.height upper)
  (level : Nat) (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

abbrev path := (Nodes.path upper).append pDown

variable
  (hnode : WholeArrayInteriorExterior.upperNode (path upper pDown) =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats (path upper pDown) projected)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

abbrev Raw := CutChildGrouping.Raw (C := LowerCutPair.Calls rows repeats (path upper pDown))
  (cutSlots (path upper pDown) projected) rows

def tape (raw : Raw (rows := rows) (repeats := repeats) projected upper pDown) :
    WholeCutSampler.Tape rows repeats (path upper pDown) projected :=
  (splitTape rows repeats (path upper pDown) projected).symm (exterior, raw)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)

def knownRaw (raw : Raw (rows := rows) (repeats := repeats) projected upper pDown) :
    HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper :=
  WholeCutSubtree.knownBucketsAtNode rows repeats projected upper pDown hproper (LinearMap.ker A)
    (tape projected upper pDown exterior raw)

def knownBackground
    (bg : LowerProjectedFiberAverage.Background (repeats := repeats) (path upper pDown) projected a) :
    HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper :=
  LowerCutBucketLocality.knownBucketsOfComplement rows repeats projected upper pDown hproper
    (LinearMap.ker A) exterior bg.1

theorem knownRaw_eq
    (raw : Raw (rows := rows) (repeats := repeats) projected upper pDown) :
    knownRaw projected upper pDown hproper exterior A raw =
      knownBackground projected upper pDown hproper a exterior A
        (LowerCutSingleFiberDisintegration.coordinates rows repeats (path upper pDown)
          projected a raw).1 := by
  unfold knownRaw knownBackground tape
  simpa only [LowerCutSingleFiberDisintegration.coordinates_complement] using
    (LowerCutBucketLocality.knownBucketsAtNode_join rows repeats projected upper pDown hproper
      (LinearMap.ker A) exterior raw)

variable
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

def physicalSuccess (s : Nat) : ℝ :=
  (CutChildGrouping.rawLaw (C := LowerCutPair.Calls rows repeats (path upper pDown))
    (cutSlots (path upper pDown) projected) rows).expectation (fun raw =>
      LowerProjectedOriginalSuccess.kernelSuccess (repeats := repeats) (path upper pDown) slots projected projection upper level
        hbranch d hnode a A cut σ useful ρ threshold s
        (knownRaw projected upper pDown hproper exterior A raw)
        (WholeCutSampler.evaluate rows repeats (path upper pDown) projected
          (tape projected upper pDown exterior raw)))

theorem physicalSuccess_eq_rawSuccess (s : Nat) :
    physicalSuccess slots projected projection upper pDown hproper level hbranch d hnode a exterior A
        cut σ useful ρ threshold s =
      LowerProjectedOriginalSuccess.rawSuccess (path upper pDown) slots projected projection upper level
        hbranch d hnode a exterior A cut σ useful ρ threshold
        (knownBackground projected upper pDown hproper a exterior A) s := by
  unfold physicalSuccess LowerProjectedOriginalSuccess.rawSuccess
  apply FiniteDistribution.expectation_congr
  intro raw
  exact congrArg
    (fun known => LowerProjectedOriginalSuccess.kernelSuccess (repeats := repeats) (path upper pDown) slots projected
      projection upper level hbranch d hnode a A cut σ useful ρ threshold s known
      (LowerCutRows.reconstruct rows repeats (path upper pDown) projected exterior raw))
    (knownRaw_eq projected upper pDown hproper a exterior A raw)

theorem physicalSuccess_square_le (s : Nat) :
    physicalSuccess slots projected projection upper pDown hproper level hbranch d hnode a exterior A
        cut σ useful ρ threshold s ^ 2 ≤
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
        (LowerProjectedFiberAverage.rawCollision (path upper pDown) slots projected projection upper level
          hbranch d a exterior A s) := by
  rw [physicalSuccess_eq_rawSuccess]
  exact LowerProjectedOriginalSuccess.rawSuccess_square_le (path upper pDown) slots projected projection
    upper level hbranch d hnode a exterior A cut σ useful ρ threshold
    (knownBackground projected upper pDown hproper a exterior A) s

end
end PerfectCompleteness.LowerPhysicalFiberSuccess

end

end OAI
