import OAI.Computability.PerfectCompleteness.Decoding.OriginalWholeCutProjection
import OAI.Computability.PerfectCompleteness.Decoding.SelectedArrayProjection
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutReconstructionLemmas
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutReference
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarFreshProjectionLemmas

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i t : Nat}

def oldRecordPullback (rows repeats : Nat → Nat) (p : Path branch n (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (record : OriginalWholeCut.Record rows repeats p right) :
    OriginalWholeCut.Record rows repeats p left :=
  (OriginalWholeCutProjection.exteriorEquiv rows repeats p right left
      (fun s h => (hs s h).symm) record.1,
    ChildAssemblyProjection.assembledPullback rows (CutGroupedProjection.cutProjection p q) record.2)

theorem reconstruct_pullback (rows repeats : Nat → Nat) (p : Path branch n (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats p right) :
    OriginalWholeCut.reconstructRecord rows repeats p left
        (oldRecordPullback rows repeats p left right q hs record) =
      ChildBlockProjection.arraysPullback rows q
        (OriginalWholeCut.reconstructRecord rows repeats p right record) :=
  OriginalWholeCutProjection.reconstruct_pullback rows repeats p left right q hs hk
    record.1 record.2.1 record.2.2

theorem rootBuckets_pullback (rows repeats : Nat → Nat)
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch (j + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside r s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside r s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats r right) :
    UpperScalarCutBucket.rootBuckets rows repeats r left
        (oldRecordPullback rows repeats r left right q hs record) =
      fun a => HPullback q (UpperScalarCutBucket.rootBuckets rows repeats r right record a) := by
  cases r with
  | refl => rfl
  | step child r =>
      funext a
      unfold oldRecordPullback
      rw [OriginalWholeCutProjection.exteriorEquiv_step rows repeats child r left right hs record.1]
      exact OriginalScalarProjection.reconstruct_pullback repeats (.step child r)
        left right q hs hk (fun terminal => record.2.1 (.inl (a, terminal))) (record.1.1 a)

theorem upperBuckets_pullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1)) :
    ∀ (r : Path branch (j + 1) (i + 1))
      (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s),
      (∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k))) →
      ∀ (record : OriginalWholeCut.Record rows repeats (p.append r) right),
    UpperScalarCutBucket.upperBuckets rows repeats p r left
        (oldRecordPullback rows repeats (p.append r) left right q hs record) =
      fun a => HPullback (CutGroupedProjection.cutProjection p q)
        (UpperScalarCutBucket.upperBuckets rows repeats p r right record a) := by
  induction n generalizing j with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro r left right q hs hk record
          exact rootBuckets_pullback rows repeats r left right q hs hk record
      | step child p =>
          intro r left right q hs hk record
          unfold oldRecordPullback
          have hext := OriginalWholeCutProjection.exteriorEquiv_step rows repeats child
            (p.append r) left right hs record.1
          refine (congrArg (fun exterior : OriginalWholeCutTape.Exterior rows repeats
              ((Path.step child p).append r) left =>
            UpperScalarCutBucket.upperBuckets rows repeats (.step child p) r left
              (exterior, ChildAssemblyProjection.assembledPullback rows
                (CutGroupedProjection.cutProjection ((Path.step child p).append r) q)
                record.2)) hext).trans ?_
          exact ih p r (childSlots left child) (childSlots right child) (fun s k => q (child, s) k)
            (fun s h => hs (child, s) (WholeCutExteriorTransport.outside_selected child (p.append r) s h))
            (fun s h k => hk (child, s) (WholeCutExteriorTransport.outside_selected child (p.append r) s h) k)
            (record.1.2.1, (fun call => record.2.1 (.inr call), record.2.2))

theorem map_updated_buckets {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module F2 A] [Module F2 B] {w : Nat} (f : A →ₗ[F2] B)
    (buckets : BucketSampler.Tape w A) (a : BucketSampler.Direction w) (fresh : A) :
    BucketSampler.evaluate w id (Function.update (fun b => f (buckets b)) a (f fresh)) =
      fun row => f (BucketSampler.evaluate w id (Function.update buckets a fresh) row) := by
  have hupdate : Function.update (fun b => f (buckets b)) a (f fresh) =
      fun b => f (Function.update buckets a fresh b) := by
    funext b
    by_cases h : b = a <;> simp [h]
  rw [hupdate]
  funext row
  simp only [BucketSampler.evaluate, id_eq, map_sum, map_smul]

theorem replaceArrays_pullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats (p.append r) right)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p right)) :
    UpperScalarCutBucket.replaceArrays rows repeats p r left
        (oldRecordPullback rows repeats (p.append r) left right q hs record) a
        (HPullback (CutGroupedProjection.cutProjection p q) fresh) =
      ChildBlockProjection.arraysPullback rows q
        (UpperScalarCutBucket.replaceArrays rows repeats p r right record a fresh) := by
  unfold UpperScalarCutBucket.replaceArrays
  rw [reconstruct_pullback rows repeats (p.append r) left right q hs hk,
    upperBuckets_pullback rows repeats p r left right q hs hk,
    map_updated_buckets]
  exact SelectedArrayProjection.replace_pullback rows p left right q _ _

def projectedPair (rows : Nat → Nat) (p : Path branch n (j + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (arrays : Arrays right rows)
    (buckets : BucketSampler.Tape (rows (j + 1)) (H (cutSlots p right)))
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p right)) :
    HierarchicalAgreementMean.PairRecord (rows := rows) left (upperNode p) :=
  (HierarchicalMatrixTable.backgroundOf left (upperNode p)
      (ChildBlockProjection.arraysPullback rows q arrays),
    (NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows q arrays) (upperNode p),
      NodeEmbedding.matrix (ChildBlockProjection.arraysPullback rows q
        (SelectedArrayReplacement.replace rows p right arrays
          (BucketSampler.evaluate (rows (j + 1)) id (Function.update buckets a fresh)))) (upperNode p)))

theorem pairRecord_pullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats (p.append r) right)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p right)) :
    UpperScalarCutBucket.pairRecord rows repeats p r left
        (oldRecordPullback rows repeats (p.append r) left right q hs record) a
        (HPullback (CutGroupedProjection.cutProjection p q) fresh) =
      projectedPair rows p left right q
        (OriginalWholeCut.reconstructRecord rows repeats (p.append r) right record)
        (UpperScalarCutBucket.upperBuckets rows repeats p r right record) a fresh := by
  unfold UpperScalarCutBucket.pairRecord projectedPair
  rw [reconstruct_pullback rows repeats (p.append r) left right q hs hk,
    replaceArrays_pullback rows repeats p r left right q hs hk]
  rfl

def exteriorEquiv (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    UpperScalarCutReconstruction.Exterior rows repeats p r right ≃
      UpperScalarCutReconstruction.Exterior rows repeats p r left :=
  Equiv.prodCongr
    (OriginalWholeCutProjection.exteriorEquiv rows repeats (p.append r) right left
      (fun s h => (hs s h).symm))
    (UpperScalarFreshProjection.freshExteriorEquiv repeats p r left right hs)

theorem exteriorEquiv_law (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    (UpperScalarCutLaw.exteriorLaw rows repeats p r right).pushforward
        (exteriorEquiv rows repeats p r left right hs) =
      UpperScalarCutLaw.exteriorLaw rows repeats p r left := by
  unfold UpperScalarCutLaw.exteriorLaw
  change ((OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) right).product
    (UpperScalarCutLaw.freshExteriorLaw repeats p r right)).pushforward (fun z =>
    (OriginalWholeCutProjection.exteriorEquiv rows repeats (p.append r) right left
      (fun s h => (hs s h).symm) z.1,
      UpperScalarFreshProjection.freshExteriorEquiv repeats p r left right hs z.2)) = _
  rw [FiniteDistribution.product_pushforward
    (OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) right)
    (UpperScalarCutLaw.freshExteriorLaw repeats p r right)
    (OriginalWholeCutProjection.exteriorEquiv rows repeats (p.append r) right left
      (fun s h => (hs s h).symm))
    (UpperScalarFreshProjection.freshExteriorEquiv repeats p r left right hs),
    OriginalWholeCutProjection.exteriorEquiv_law,
    UpperScalarFreshProjection.freshExteriorEquiv_law]

def recordPullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (record : UpperScalarCutReconstruction.Record rows repeats p r right) :
    UpperScalarCutReconstruction.Record rows repeats p r left :=
  (exteriorEquiv rows repeats p r left right hs record.1,
    ChildAssemblyProjection.assembledPullback rows
      (CutGroupedProjection.cutProjection (p.append r) q) record.2)

def numberedRecordPullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (record : UpperScalarCutReconstruction.NumberedRecord rows repeats p r right) :
    UpperScalarCutReconstruction.NumberedRecord rows repeats p r left :=
  (exteriorEquiv rows repeats p r left right hs record.1,
    ChildAssemblyProjection.assembledPullback rows
      (CutGroupedProjection.cutProjection (p.append r) q) record.2)

theorem enlargedPairRecord_pullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (a : BucketSampler.Direction (rows (j + 1)))
    (record : UpperScalarCutReconstruction.Record rows repeats p r right) :
    UpperScalarCutBucket.enlargedPairRecord rows repeats p r left
        (a, recordPullback rows repeats p r left right q hs record) =
      projectedPair rows p left right q
        (OriginalWholeCut.reconstructRecord rows repeats (p.append r) right
          (UpperScalarCutReconstruction.oldRecord rows repeats p r right record))
        (UpperScalarCutBucket.upperBuckets rows repeats p r right
          (UpperScalarCutReconstruction.oldRecord rows repeats p r right record)) a
        (UpperScalarCutReconstruction.reconstructFresh repeats p r right
          (UpperScalarCutReconstruction.freshRecord rows repeats p r right record)) := by
  change UpperScalarCutBucket.pairRecord rows repeats p r left
    (oldRecordPullback rows repeats (p.append r) left right q hs
      (UpperScalarCutReconstruction.oldRecord rows repeats p r right record)) a
    (UpperScalarCutReconstruction.reconstructFresh repeats p r left
      (fun call => HPullback (CutGroupedProjection.cutProjection (p.append r) q)
          (record.2.1 (.inr call)),
        UpperScalarFreshProjection.freshExteriorEquiv repeats p r left right hs record.1.2)) = _
  rw [UpperScalarFreshProjection.reconstructFresh_pullback repeats p r left right q hs hk]
  exact pairRecord_pullback rows repeats p r left right q hs hk _ a _

theorem numberedPairRecord_pullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (a : BucketSampler.Direction (rows (j + 1)))
    (record : UpperScalarCutReconstruction.Record rows repeats p r right) :
    UpperScalarCutBucket.numberedPairRecord rows repeats p r left
        (a, numberedRecordPullback rows repeats p r left right q hs
          (UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r right record)) =
      projectedPair rows p left right q
        (OriginalWholeCut.reconstructRecord rows repeats (p.append r) right
          (UpperScalarCutReconstruction.oldRecord rows repeats p r right record))
        (UpperScalarCutBucket.upperBuckets rows repeats p r right
          (UpperScalarCutReconstruction.oldRecord rows repeats p r right record)) a
        (UpperScalarCutReconstruction.reconstructFresh repeats p r right
          (UpperScalarCutReconstruction.freshRecord rows repeats p r right record)) := by
  have hnumber : numberedRecordPullback rows repeats p r left right q hs
      (UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r right record) =
    UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r left
      (recordPullback rows repeats p r left right q hs record) := rfl
  rw [hnumber, UpperScalarCutBucket.numberedPairRecord_numberRecord]
  exact enlargedPairRecord_pullback rows repeats p r left right q hs hk a record

def stoppedProjectedPair (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (sample : BucketSampler.Direction (rows (j + 1)) ×
      (WholeArraySampler.Tape rows repeats (p.append r) right × H (cutSlots p right))) :
    HierarchicalAgreementMean.PairRecord (rows := rows) left (upperNode p) :=
  projectedPair rows p left right q
    (WholeArraySampler.evaluate rows repeats (p.append r) right sample.2.1)
    (UpperStoppedBuckets.stoppedBuckets rows repeats p r hproper right sample.2.1)
    sample.1 sample.2.2

private def stoppedRead (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : UpperScalarCutReconstruction.Record rows repeats p r slots) :
    WholeArraySampler.Tape rows repeats (p.append r) slots × H (cutSlots p slots) :=
  (OriginalUniformCut.toStoppedTape rows repeats (p.append r) slots
      (UpperScalarCutReconstruction.oldRecord rows repeats p r slots record),
    UpperScalarCutReconstruction.reconstructFresh repeats p r slots
      (UpperScalarCutReconstruction.freshRecord rows repeats p r slots record))

private theorem numberedPairRecord_stoppedRead (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (hproper : i + 1 < j + 1)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (a : BucketSampler.Direction (rows (j + 1)))
    (record : UpperScalarCutReconstruction.Record rows repeats p r right) :
    UpperScalarCutBucket.numberedPairRecord rows repeats p r left
        (a, numberedRecordPullback rows repeats p r left right q hs
          (UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r right record)) =
      stoppedProjectedPair rows repeats p r hproper left right q
        (a, stoppedRead rows repeats p r right record) := by
  rw [numberedPairRecord_pullback rows repeats p r left right q hs hk]
  unfold stoppedProjectedPair stoppedRead
  rw [OriginalUniformCut.evaluate_toStoppedTape,
    ← UpperStoppedBuckets.upperBuckets_toStoppedTape]

attribute [local instance] linearMapFintype

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

private theorem product_push_right {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (f : B → C) :
    (μ.product ν).pushforward (fun z => (z.1, f z.2)) = μ.product (ν.pushforward f) := by
  simpa only [FiniteDistribution.pushforward_id, id_eq] using
    (FiniteDistribution.product_pushforward μ ν id f)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype in
private theorem stoppedRead_law (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (UpperScalarCutReference.referenceLaw rows repeats p r slots).pushforward
        (stoppedRead rows repeats p r slots) =
      (WholeArraySampler.tapeLaw rows repeats (p.append r) slots).product
        (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p slots))) := by
  rw [← UpperScalarCutReference.pack_referenceLaw rows repeats p r slots,
    FiniteDistribution.pushforward_comp]
  change ((OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).product
    (UpperScalarCutReference.freshReferenceLaw repeats p r slots)).pushforward
      (fun z => (OriginalUniformCut.toStoppedTape rows repeats (p.append r) slots z.1,
        UpperScalarCutReconstruction.reconstructFresh repeats p r slots z.2)) = _
  rw [FiniteDistribution.product_pushforward
    (OriginalUniformCut.referenceLaw rows repeats (p.append r) slots)
    (UpperScalarCutReference.freshReferenceLaw repeats p r slots)
    (OriginalUniformCut.toStoppedTape rows repeats (p.append r) slots)
    (UpperScalarCutReconstruction.reconstructFresh repeats p r slots),
    UpperStoppedBuckets.reference_toStoppedTape,
    UpperScalarCutReference.reconstructFresh_referenceLaw]

theorem fixed_projected_law (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (directions.product ((UpperScalarCutLaw.exteriorLaw rows repeats p r left).product
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
        (cutSlots (p.append r) right) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows
            (CutGroupedProjection.cutProjection (p.append r) q))))).pushforward
              (UpperScalarCutBucket.numberedPairRecord rows repeats p r left) =
      (directions.product ((WholeArraySampler.tapeLaw rows repeats (p.append r) right).product
        (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p right))))).pushforward
          (stoppedProjectedPair rows repeats p r hproper left right q) := by
  have hlift : (UpperScalarCutReference.numberedReferenceLaw rows repeats p r right).pushforward
      (numberedRecordPullback rows repeats p r left right q hs) =
    (UpperScalarCutLaw.exteriorLaw rows repeats p r left).product
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
        (cutSlots (p.append r) right) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows
            (CutGroupedProjection.cutProjection (p.append r) q))) := by
    unfold UpperScalarCutReference.numberedReferenceLaw numberedRecordPullback
    rw [FiniteDistribution.product_pushforward
      (UpperScalarCutLaw.exteriorLaw rows repeats p r right)
      (FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
        (cutSlots (p.append r) right) rows))
      (exteriorEquiv rows repeats p r left right hs)
      (ChildAssemblyProjection.assembledPullback rows
        (CutGroupedProjection.cutProjection (p.append r) q)), exteriorEquiv_law]
  rw [← hlift, ← product_push_right, FiniteDistribution.pushforward_comp,
    ← UpperScalarCutReference.numberRecord_referenceLaw rows repeats p r right,
    ← product_push_right, FiniteDistribution.pushforward_comp]
  have hmap :
      (fun sample : BucketSampler.Direction (rows (j + 1)) ×
          UpperScalarCutReconstruction.Record rows repeats p r right =>
        UpperScalarCutBucket.numberedPairRecord rows repeats p r left
          (sample.1, numberedRecordPullback rows repeats p r left right q hs
            (UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r right sample.2))) =
      (fun sample => stoppedProjectedPair rows repeats p r hproper left right q
        (sample.1, stoppedRead rows repeats p r right sample.2)) := by
    funext sample
    exact numberedPairRecord_stoppedRead rows repeats p r hproper left right q hs hk sample.1 sample.2
  rw [hmap, ← FiniteDistribution.pushforward_comp
    (directions.product (UpperScalarCutReference.referenceLaw rows repeats p r right))
    (fun sample => (sample.1, stoppedRead rows repeats p r right sample.2))
    (stoppedProjectedPair rows repeats p r hproper left right q),
    product_push_right, stoppedRead_law]

end
end PerfectCompleteness.UpperScalarCutProjection

end

end OAI
