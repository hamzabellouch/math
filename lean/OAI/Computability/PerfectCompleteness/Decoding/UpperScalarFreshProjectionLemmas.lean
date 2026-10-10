import OAI.Computability.PerfectCompleteness.Decoding.CutGroupedProjectionLemmas
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutLaw
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutReconstructionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedPrefixComparison
import OAI.Computability.PerfectCompleteness.Sampling.OriginalUniformCut

namespace OAI

section

namespace PerfectCompleteness.UpperScalarFreshProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i t : Nat}

theorem outside_append (p : Path branch n j) (r : Path branch j i)
    (s : Slots branch j) (hs : WholeCutExteriorTransport.Outside r s) :
    WholeCutExteriorTransport.Outside (p.append r) (p.slotEmbedding s) := by
  rintro ⟨u, hu⟩
  apply hs
  refine ⟨u, p.slotEmbedding_injective ?_⟩
  exact (p.slotEmbedding_append r u).symm.trans hu

theorem restricted_outside_eq (p : Path branch n j) (r : Path branch j i)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    ∀ s, WholeCutExteriorTransport.Outside r s → cutSlots p left s = cutSlots p right s :=
  fun s h => hs (p.slotEmbedding s) (outside_append p r s h)

theorem restricted_keep (p : Path branch n j) (r : Path branch j i)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ a,
      HEq (q s a) (MixedSupport.Projection.keep (left s a))) :
    ∀ s, WholeCutExteriorTransport.Outside r s → ∀ a,
      HEq (q (p.slotEmbedding s) a) (MixedSupport.Projection.keep (cutSlots p left s a)) :=
  fun s h a => hk (p.slotEmbedding s) (outside_append p r s h) a

def freshExteriorEquiv (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    FreshExterior repeats p r right ≃ FreshExterior repeats p r left :=
  Equiv.cast (OriginalScalarProjection.scalarExterior_eq repeats r
    (cutSlots p right) (cutSlots p left)
    (fun s h => (restricted_outside_eq p r left right hs s h).symm))

theorem freshExteriorEquiv_law (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s) :
    (UpperScalarCutLaw.freshExteriorLaw repeats p r right).pushforward
        (freshExteriorEquiv repeats p r left right hs) =
      UpperScalarCutLaw.freshExteriorLaw repeats p r left := by
  simp only [UpperScalarCutLaw.freshExteriorLaw, OriginalTerminalSplit.exteriorLaw_uniform]
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (freshExteriorEquiv repeats p r left right hs)

theorem cutSpaceEquiv_HPullback (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1))
      (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
      (f : H (cutSlots (p.append r) right)),
      cutSpaceEquiv p r left
          (HPullback (CutGroupedProjection.cutProjection (p.append r) q) f) =
        HPullback (CutGroupedProjection.cutProjection r (fun s a => q (p.slotEmbedding s) a))
          (cutSpaceEquiv p r right f) := by
  induction p with
  | refl j => intro r left right q f; rfl
  | step child p ih =>
      intro r left right q f
      exact ih r (childSlots left child) (childSlots right child)
        (ChildAssemblyProjection.childProjection q child) f

theorem reconstructFresh_pullback (repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ a,
      HEq (q s a) (MixedSupport.Projection.keep (left s a)))
    (values : FreshValues repeats p r right) (exterior : FreshExterior repeats p r right) :
    reconstructFresh repeats p r left
        (fun call => HPullback (CutGroupedProjection.cutProjection (p.append r) q) (values call),
          freshExteriorEquiv repeats p r left right hs exterior) =
      HPullback (CutGroupedProjection.cutProjection p q)
        (reconstructFresh repeats p r right (values, exterior)) := by
  have hvalues :
      (fun call : TerminalCalls.TerminalIndex repeats r =>
        cutSpaceEquiv p r left
          (HPullback (CutGroupedProjection.cutProjection (p.append r) q) (values call))) =
      (fun call => HPullback
        (CutGroupedProjection.cutProjection r (CutGroupedProjection.cutProjection p q))
        (cutSpaceEquiv p r right (values call))) := by
    funext call
    exact cutSpaceEquiv_HPullback p r left right q (values call)
  unfold reconstructFresh
  rw [hvalues]
  exact OriginalScalarProjection.reconstruct_pullback repeats r
    (cutSlots p left) (cutSlots p right) (CutGroupedProjection.cutProjection p q)
    (restricted_outside_eq p r left right hs) (restricted_keep p r left right q hk)
    (fun call => cutSpaceEquiv p r right (values call)) exterior

end
end PerfectCompleteness.UpperScalarFreshProjection

end

section

namespace PerfectCompleteness.UpperScalarPairComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n j i k t : Nat} {K : Type*} [Fintype K]

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

def pairLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (assembled : FiniteDistribution (CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
      (cutSlots (p.append r) slots) rows)) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p)) :=
  (directions.product ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    assembled)).pushforward (UpperScalarCutBucket.numberedPairRecord rows repeats p r slots)

theorem variation_le (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (P Q : FiniteDistribution (CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
      (cutSlots (p.append r) slots) rows)) :
    (pairLaw rows repeats p r slots directions P).totalVariation
      (pairLaw rows repeats p r slots directions Q) ≤ P.totalVariation Q := by
  have h := CommonProductVariation.observed_product_le directions
    ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product P)
    ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product Q)
    (UpperScalarCutBucket.numberedPairRecord rows repeats p r slots)
  simpa only [pairLaw, CommonProductVariation.product_totalVariation] using h

variable {Z : Fin (branch i) → Type*} [∀ c, Fintype (Z c)]

theorem modified_original_variation (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (c : Fin (branch i)) → Z c → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ c z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append r) slots) c s a) (projected c z s a))
    (choiceLaw : (c : Fin (branch i)) → FiniteDistribution (Z c))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : FiniteDistribution K) (q : K → Path branch i k) (hbranch : 0 < branch i)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (pairLaw rows repeats p r slots directions
      (ProjectedPrefixComparison.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
        (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ')).totalVariation
      (pairLaw rows repeats p r slots directions
        (OriginalPrefixContinuation.assembledLaw
          (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows repeats
          (cutSlots (p.append r) slots) ν q hbranch)) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) - 1)) ^ branch i - 1) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows : ℝ) ^ 2 / branch i) / 2 :=
  (variation_le rows repeats p r slots directions _ _).trans
    (ProjectedPrefixComparison.original_variation
      (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows repeats
      (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ' ν q hbranch)

end
end PerfectCompleteness.UpperScalarPairComparison

end

section

namespace PerfectCompleteness.UpperStoppedBuckets

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

attribute [local instance 2000] OriginalUniformCutBase.valuesChildrenFintype

variable {branch : Nat → Nat} {n j i t : Nat}

def stoppedRootBuckets (rows repeats : Nat → Nat) :
    {j i : Nat} → (r : Path branch (j + 1) (i + 1)) → i + 1 < j + 1 →
      (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot) →
        WholeArraySampler.Tape rows repeats r slots →
          BucketSampler.Tape (rows (j + 1)) (H slots)
  | _, _, .refl _, hproper, _, _, _ => False.elim ((Nat.lt_irrefl _) hproper)
  | _, _, .step child r, _, slots, tape, direction =>
      RecursiveSampler.evaluate F2 repeats (.step child r) (LeafDomain slots)
        (tape (.inl ()) direction)

def stoppedBuckets (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append r) slots) :
    BucketSampler.Tape (rows (j + 1)) (H (cutSlots p slots)) :=
  stoppedRootBuckets rows repeats r hproper (cutSlots p slots)
    (WholeArraySubtreeSplit.extract rows repeats p r slots tape)

theorem extract_toStoppedTape (rows repeats : Nat → Nat) (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (record : Record rows repeats (p.append r) slots),
      WholeArraySubtreeSplit.extract rows repeats p r slots
          (OriginalUniformCut.toStoppedTape rows repeats (p.append r) slots record) =
        OriginalUniformCut.toStoppedTape rows repeats r (cutSlots p slots)
          (UpperScalarCutBucket.descendRecord rows repeats p r slots record) := by
  induction p with
  | refl n =>
      intro r slots record
      cases r <;> rfl
  | step child p ih =>
      intro r slots record
      exact ih r (childSlots slots child)
        (record.1.2.1, (fun call => record.2.1 (.inr call), record.2.2))

theorem rootBuckets_toStoppedTape (rows repeats : Nat → Nat)
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot)
    (record : Record rows repeats r slots) :
    UpperScalarCutBucket.rootBuckets rows repeats r slots record =
      stoppedRootBuckets rows repeats r hproper slots
        (OriginalUniformCut.toStoppedTape rows repeats r slots record) := by
  cases r with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step child r => rfl

theorem upperBuckets_toStoppedTape (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (hproper : i + 1 < j + 1)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats (p.append r) slots) :
    UpperScalarCutBucket.upperBuckets rows repeats p r slots record =
      stoppedBuckets rows repeats p r hproper slots
        (OriginalUniformCut.toStoppedTape rows repeats (p.append r) slots record) :=
  (rootBuckets_toStoppedTape rows repeats r hproper (cutSlots p slots)
    (UpperScalarCutBucket.descendRecord rows repeats p r slots record)).trans
    (congrArg (stoppedRootBuckets rows repeats r hproper (cutSlots p slots))
      (extract_toStoppedTape rows repeats p r slots record)).symm

theorem reference_toStoppedTape (rows repeats : Nat → Nat)
    (p : Path branch n (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalUniformCut.referenceLaw rows repeats p slots).pushforward
        (OriginalUniformCut.toStoppedTape rows repeats p slots) =
      WholeArraySampler.tapeLaw rows repeats p slots := by
  rw [OriginalUniformCut.referenceLaw_uniform, OriginalUniformCut.uniform_toStoppedTape,
    WholeArraySubtreeSplit.tapeLaw_eq_uniform]

theorem joint_referenceLaw (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (hproper : i + 1 < j + 1)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).pushforward
        (fun record => (reconstructRecord rows repeats (p.append r) slots record,
          UpperScalarCutBucket.upperBuckets rows repeats p r slots record)) =
      (WholeArraySampler.tapeLaw rows repeats (p.append r) slots).pushforward
        (fun tape => (WholeArraySampler.evaluate rows repeats (p.append r) slots tape,
          stoppedBuckets rows repeats p r hproper slots tape)) := by
  calc
    _ = ((OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).pushforward
        (OriginalUniformCut.toStoppedTape rows repeats (p.append r) slots)).pushforward
          (fun tape => (WholeArraySampler.evaluate rows repeats (p.append r) slots tape,
            stoppedBuckets rows repeats p r hproper slots tape)) := by
      rw [FiniteDistribution.pushforward_comp]
      congr 1
      funext record
      exact Prod.ext
        (OriginalUniformCut.evaluate_toStoppedTape rows repeats (p.append r) slots record).symm
        (upperBuckets_toStoppedTape rows repeats p r hproper slots record)
    _ = _ := by rw [reference_toStoppedTape]

end
end PerfectCompleteness.UpperStoppedBuckets

end

end OAI
