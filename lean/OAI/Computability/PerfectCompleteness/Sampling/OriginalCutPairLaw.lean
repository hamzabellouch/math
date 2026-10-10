import OAI.Computability.PerfectCompleteness.Construction.CutBucketTransportLemmas
import OAI.Computability.PerfectCompleteness.Sampling.OriginalCutBucketLaw

namespace OAI

section

namespace PerfectCompleteness.OriginalCutPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m k t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

theorem matrix_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots) :
    NodeEmbedding.matrix (OriginalWholeCut.reconstructRecord rows repeats p slots record)
        (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (CutNodeRows.bucketTapeEquiv rows p slots
          (OriginalCutBucketReplacement.ownValues rows repeats p slots record.2.1)) := by
  rw [← CutNodeRows.matrixOfRows_selectedRows]
  change CutNodeRows.matrixOfRows rows p slots
    (SelectedArrayReplacement.selectedRows rows p slots
      (OriginalWholeCut.reconstruct rows repeats p slots record.1 record.2.1 record.2.2)) = _
  rw [OriginalCutBucketReplacement.selectedRows_reconstruct]
  exact CutNodeRows.matrixOfRows_evaluate rows p slots _

def transportPair (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : OriginalCutBucketLaw.NativeSample rows p slots) :
    OriginalCutCollision.PairRecord rows p slots :=
  HierarchicalAgreementMean.pairRecord slots (upperNode p)
    (sample.1, CutNodeRows.bucketSampleEquiv rows p slots sample.2)

private theorem transportPair_law (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (μ : FiniteDistribution (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)))
    (ν : FiniteDistribution (BucketSampler.Direction (rows (m + 1)) ×
      (BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots)) × H (cutSlots p slots)))) :
    (μ.product ν).pushforward (transportPair rows p slots) =
      ((μ.product ν).pushforward
        (fun z : OriginalCutBucketLaw.NativeSample rows p slots =>
          (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))).pushforward
        (HierarchicalAgreementMean.pairRecord slots (upperNode p)) := by
  exact (FiniteDistribution.pushforward_comp (μ.product ν)
    (fun z : OriginalCutBucketLaw.NativeSample rows p slots =>
      (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))
    (HierarchicalAgreementMean.pairRecord slots (upperNode p))).symm

theorem pairRecord_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (m + 1)) ×
      OriginalExtraCutComparison.Record rows repeats p slots) :
    OriginalCutCollision.pairRecord rows repeats p slots sample =
      transportPair rows p slots (OriginalCutBucketLaw.read rows repeats p slots sample) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change NodeEmbedding.matrix
        (OriginalWholeCut.reconstructRecord rows repeats p slots
          (OriginalCutCollision.oldRecord rows repeats p slots sample.2)) (upperNode p) = _
      rw [matrix_reconstruct]
      rfl
    · change NodeEmbedding.matrix
        (OriginalWholeCut.reconstructRecord rows repeats p slots
          (OriginalCutBucketReplacement.replaceRecord rows repeats p slots
            (OriginalCutCollision.oldRecord rows repeats p slots sample.2) sample.1 sample.2.2))
          (upperNode p) = _
      rw [matrix_reconstruct]
      change BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (CutNodeRows.bucketTapeEquiv rows p slots
          (OriginalCutBucketReplacement.ownValues rows repeats p slots
            (OriginalCutBucketReplacement.replaceValues rows repeats p slots
              (OriginalCutCollision.oldRecord rows repeats p slots sample.2).2.1
                sample.1 sample.2.2))) = _
      rw [OriginalCutBucketReplacement.ownValues_replaceValues,
        CutNodeRows.bucketTapeEquiv_update]
      rfl

def directionsLaw (rows : Nat → Nat) (m : Nat) (hrows : 0 < rows (m + 1)) :
    FiniteDistribution (BucketSampler.Direction (rows (m + 1))) := by
  letI : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact FiniteDistribution.uniform _

theorem reference_pair_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (hrows : 0 < rows (m + 1)) :
    ((directionsLaw rows m hrows).product
      (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
        (OriginalCutCollision.pairRecord rows repeats p slots) =
      HierarchicalAgreementMean.referenceLaw slots (upperNode p)
        (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
        (by simpa only [upperNode_height] using hrows) := by
  let μ := OriginalOwnBucketSplit.backgroundLaw rows repeats p slots
  have hread := OriginalCutBucketLaw.reference_read_law rows repeats p slots
    (directionsLaw rows m hrows)
  have hnative :
      ((directionsLaw rows m hrows).product
        (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
          (OriginalCutBucketLaw.read rows repeats p slots) =
        μ.product (CutBucketTransport.nativeLaw rows p slots hrows) := by
    simpa only [μ, CutBucketTransport.nativeLaw, directionsLaw,
      BucketSampler.tapeLaw, UniformLinearImage.law_uniform] using hread
  have htransport := FiniteDistribution.product_pushforward μ
    (CutBucketTransport.nativeLaw rows p slots hrows) id
    (CutNodeRows.bucketSampleEquiv rows p slots)
  simp only [id_eq, FiniteDistribution.pushforward_id] at htransport
  calc
    _ = (((directionsLaw rows m hrows).product
        (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
          (OriginalCutBucketLaw.read rows repeats p slots)).pushforward
            (transportPair rows p slots) := by
      rw [FiniteDistribution.pushforward_comp]
      congr 1
      funext sample
      exact pairRecord_eq rows repeats p slots sample
    _ = (μ.product (CutBucketTransport.nativeLaw rows p slots hrows)).pushforward
        (transportPair rows p slots) := by rw [hnative]
    _ = ((μ.product (CutBucketTransport.nativeLaw rows p slots hrows)).pushforward
        (fun z => (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))).pushforward
          (HierarchicalAgreementMean.pairRecord slots (upperNode p)) :=
      transportPair_law rows p slots μ (CutBucketTransport.nativeLaw rows p slots hrows)
    _ = _ := by
      rw [htransport, CutBucketTransport.nativeLaw_pushforward]
      rfl

theorem actual_pair_totalVariation_le {K : Type*} [Fintype K]
    (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (hrows : 0 < rows (m + 1)) :
    (((directionsLaw rows m hrows).product
      (OriginalExtraCutComparison.actualLaw rows repeats p slots ν q hbranch)).pushforward
        (OriginalCutCollision.pairRecord rows repeats p slots)).totalVariation
      (HierarchicalAgreementMean.referenceLaw slots (upperNode p)
        (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
        (by simpa only [upperNode_height] using hrows)) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 := by
  rw [← reference_pair_law rows repeats p slots hrows]
  exact OriginalCutCollision.pair_totalVariation_le rows repeats p slots ν q hbranch
    (directionsLaw rows m hrows)

end
end PerfectCompleteness.OriginalCutPairLaw

end

end OAI
