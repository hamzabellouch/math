import OAI.Computability.PerfectCompleteness.Construction.CutBucketTransportLemmas
import OAI.Computability.PerfectCompleteness.Sampling.OriginalCutPairLaw

namespace OAI

section

namespace PerfectCompleteness.OriginalUsefulPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

private theorem product_mixture_pushforward {E A B Γ : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype Γ]
    (μ : FiniteDistribution A) (κ : FiniteDistribution E)
    (ν : E → FiniteDistribution B) (f : A × B → Γ) :
    (μ.product (κ.mixture ν)).pushforward f =
      κ.mixture (fun e => (μ.product (ν e)).pushforward f) := by
  have hp : μ.product (κ.mixture ν) = κ.mixture (fun e => μ.product (ν e)) := by
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    simp only [FiniteDistribution.product, FiniteDistribution.mixture, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact mul_left_comm _ _ _
  rw [hp, FiniteDistribution.pushforward_mixture]

private theorem nested_sigma_product_pushforward {Tag Bg Buck Γ : Type*}
    [Fintype Tag] [Fintype Bg] [Fintype Buck] [Fintype Γ]
    (μ : FiniteDistribution Tag) (β : Tag → FiniteDistribution Bg)
    (γ : Tag → FiniteDistribution Buck) (f : Bg × Buck → Γ) :
    (CompletionSoundness.sigmaLaw (CompletionSoundness.sigmaLaw μ β)
      (fun d : Σ _ : Tag, Bg => γ d.1)).pushforward
        (fun z => f (z.1.2, z.2)) =
      μ.mixture (fun tag => ((β tag).product (γ tag)).pushforward f) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.pushforward, CompletionSoundness.sigmaLaw,
    FiniteDistribution.mixture, FiniteDistribution.product, Fintype.sum_sigma,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

variable {branch : Nat → Nat} {n m k t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

private theorem transportPair_law (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (μ : FiniteDistribution (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)))
    (ν : FiniteDistribution (BucketSampler.Direction (rows (m + 1)) ×
      (BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots)) × H (cutSlots p slots)))) :
    (μ.product ν).pushforward (OriginalCutPairLaw.transportPair rows p slots) =
      ((μ.product ν).pushforward
        (fun z : OriginalCutBucketLaw.NativeSample rows p slots =>
          (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))).pushforward
        (HierarchicalAgreementMean.pairRecord slots (upperNode p)) := by
  exact (FiniteDistribution.pushforward_comp (μ.product ν)
    (fun z : OriginalCutBucketLaw.NativeSample rows p slots =>
      (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))
    (HierarchicalAgreementMean.pairRecord slots (upperNode p))).symm

theorem record_fresh_pair_law (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (hrows : 0 < rows (m + 1)) :
    ((OriginalCutPairLaw.directionsLaw rows m hrows).product
      (((OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
          (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))))).pushforward
      (OriginalCutCollision.pairRecord rows repeats p slots) =
      ((OriginalOwnBucketSplit.actualBackgroundLaw rows repeats p chosen q slots).product
        (HierarchicalUsefulCollision.bucketLaw slots (upperNode p)
          ((RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))).pushforward
            (CutNodeRows.cutRowEquiv p slots))
          (by simpa only [upperNode_height] using hrows))).pushforward
            (HierarchicalAgreementMean.pairRecord slots (upperNode p)) := by
  let μ := OriginalOwnBucketSplit.actualBackgroundLaw rows repeats p chosen q slots
  let scalar := RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots))
  let records := ((OriginalWholeCutLaw.recordLaw rows repeats p chosen q slots).pushforward
    (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product scalar
  let directions := OriginalCutPairLaw.directionsLaw rows m hrows
  have hread := OriginalCutBucketLaw.record_fresh_read_law rows repeats p chosen q slots directions
  have hnative :
      (directions.product records).pushforward (OriginalCutBucketLaw.read rows repeats p slots) =
        μ.product (CutBucketTransportActual.nativeLaw rows p slots scalar hrows) := by
    simpa only [μ, scalar, records, directions, CutBucketTransportActual.nativeLaw,
      OriginalCutPairLaw.directionsLaw] using hread
  have htransport := FiniteDistribution.product_pushforward μ
    (CutBucketTransportActual.nativeLaw rows p slots scalar hrows) id
    (CutNodeRows.bucketSampleEquiv rows p slots)
  simp only [id_eq, FiniteDistribution.pushforward_id] at htransport
  calc
    _ = ((directions.product records).pushforward
        (OriginalCutBucketLaw.read rows repeats p slots)).pushforward
          (OriginalCutPairLaw.transportPair rows p slots) := by
      rw [FiniteDistribution.pushforward_comp]
      congr 1
      funext sample
      exact OriginalCutPairLaw.pairRecord_eq rows repeats p slots sample
    _ = (μ.product (CutBucketTransportActual.nativeLaw rows p slots scalar hrows)).pushforward
        (OriginalCutPairLaw.transportPair rows p slots) := by rw [hnative]
    _ = ((μ.product (CutBucketTransportActual.nativeLaw rows p slots scalar hrows)).pushforward
        (fun z => (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))).pushforward
          (HierarchicalAgreementMean.pairRecord slots (upperNode p)) :=
      transportPair_law rows p slots μ (CutBucketTransportActual.nativeLaw rows p slots scalar hrows)
    _ = _ := by
      rw [htransport, CutBucketTransportActual.nativeLaw_pushforward]

abbrev Descriptor (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (K : Type*) :=
  Σ _ : Fin (branch m) × K,
    HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)

variable {K : Type*} [Fintype K]

def externalLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m) :
    FiniteDistribution (Descriptor rows p slots K) :=
  CompletionSoundness.sigmaLaw (OriginalPrefixContinuation.tagLaw ν hbranch)
    (fun tag => OriginalOwnBucketSplit.actualBackgroundLaw rows repeats p tag.1 (q tag.2) slots)

def background (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (descriptor : Descriptor rows p slots K) :
    HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p) := descriptor.2

def scalarLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (q : K → Path branch m k)
    (descriptor : Descriptor rows p slots K) :
    FiniteDistribution (NodeEmbedding.RowSpace slots (upperNode p)) :=
  (RecursiveSampler.law F2 repeats (.step descriptor.1.1 (q descriptor.1.2))
    (LeafDomain (cutSlots p slots))).pushforward (CutNodeRows.cutRowEquiv p slots)

theorem useful_pairLaw_eq_mixture (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (hrows : 0 < rows (m + 1)) :
    HierarchicalUsefulCollision.pairLaw slots (upperNode p)
        (externalLaw rows repeats p slots ν q hbranch) (background rows p slots)
        (scalarLaw rows repeats p slots q)
        (by simpa only [upperNode_height] using hrows) =
      (OriginalPrefixContinuation.tagLaw ν hbranch).mixture (fun tag =>
        ((OriginalOwnBucketSplit.actualBackgroundLaw rows repeats p tag.1 (q tag.2) slots).product
          (HierarchicalUsefulCollision.bucketLaw slots (upperNode p)
            ((RecursiveSampler.law F2 repeats (.step tag.1 (q tag.2))
              (LeafDomain (cutSlots p slots))).pushforward (CutNodeRows.cutRowEquiv p slots))
            (by simpa only [upperNode_height] using hrows))).pushforward
              (HierarchicalAgreementMean.pairRecord slots (upperNode p))) := by
  exact nested_sigma_product_pushforward
    (OriginalPrefixContinuation.tagLaw ν hbranch)
    (fun tag => OriginalOwnBucketSplit.actualBackgroundLaw rows repeats p tag.1 (q tag.2) slots)
    (fun tag => HierarchicalUsefulCollision.bucketLaw slots (upperNode p)
      ((RecursiveSampler.law F2 repeats (.step tag.1 (q tag.2))
        (LeafDomain (cutSlots p slots))).pushforward (CutNodeRows.cutRowEquiv p slots))
      (by simpa only [upperNode_height] using hrows))
    (HierarchicalAgreementMean.pairRecord slots (upperNode p))

theorem actual_pair_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (hrows : 0 < rows (m + 1)) :
    ((OriginalCutPairLaw.directionsLaw rows m hrows).product
      (OriginalExtraCutComparison.actualLaw rows repeats p slots ν q hbranch)).pushforward
        (OriginalCutCollision.pairRecord rows repeats p slots) =
      HierarchicalUsefulCollision.pairLaw slots (upperNode p)
        (externalLaw rows repeats p slots ν q hbranch) (background rows p slots)
        (scalarLaw rows repeats p slots q)
        (by simpa only [upperNode_height] using hrows) := by
  rw [OriginalExtraCutComparison.actualLaw_eq_mixture, product_mixture_pushforward,
    useful_pairLaw_eq_mixture rows repeats p slots ν q hbranch hrows]
  apply congrArg ((OriginalPrefixContinuation.tagLaw ν hbranch).mixture)
  funext tag
  exact record_fresh_pair_law rows repeats p tag.1 (q tag.2) slots hrows

end
end PerfectCompleteness.OriginalUsefulPairLaw

end

end OAI
