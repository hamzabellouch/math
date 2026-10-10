import OAI.Computability.PerfectCompleteness.Construction.OriginalCutBucketReplacement
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAgreementMean
import OAI.Computability.PerfectCompleteness.Foundations.OriginalExtraCutComparison

namespace OAI

section

namespace PerfectCompleteness.OriginalCutCollision

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m k t : Nat}

abbrev PairRecord (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  HierarchicalAgreementMean.PairRecord (rows := rows) slots
    (WholeArrayInteriorExterior.upperNode p)

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots
      (WholeArrayInteriorExterior.upperNode p)) := Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (WholeArrayInteriorExterior.upperNode p)) :=
  Fintype.ofFinite _

def oldRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalExtraCutComparison.Record rows repeats p slots) :
    OriginalWholeCut.Record rows repeats p slots :=
  (NumberedUniformCut.numberRecordEquiv rows repeats p slots).symm record.1

def oldArrays (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalExtraCutComparison.Record rows repeats p slots) : Arrays slots rows :=
  OriginalWholeCut.reconstructRecord rows repeats p slots (oldRecord rows repeats p slots record)

theorem oldArrays_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalExtraCutComparison.Record rows repeats p slots) :
    oldArrays rows repeats p slots record =
      OriginalWholeCutBridge.reconstruct rows repeats p slots record.1 := by
  have h := OriginalWholeCutBridge.reconstruct_numberRecord rows repeats p slots
    (oldRecord rows repeats p slots record)
  have hnumber : OriginalWholeCutBridge.numberRecord rows repeats p slots
      (oldRecord rows repeats p slots record) = record.1 := by
    change (NumberedUniformCut.numberRecordEquiv rows repeats p slots)
      ((NumberedUniformCut.numberRecordEquiv rows repeats p slots).symm record.1) = record.1
    exact (NumberedUniformCut.numberRecordEquiv rows repeats p slots).apply_symm_apply record.1
  rw [hnumber] at h
  exact h.symm

def replacementArrays (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (direction : BucketSampler.Direction (rows (m + 1)))
    (record : OriginalExtraCutComparison.Record rows repeats p slots) : Arrays slots rows :=
  OriginalWholeCut.reconstructRecord rows repeats p slots
    (OriginalCutBucketReplacement.replaceRecord rows repeats p slots
      (oldRecord rows repeats p slots record) direction record.2)

theorem replacement_background_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (direction : BucketSampler.Direction (rows (m + 1)))
    (record : OriginalExtraCutComparison.Record rows repeats p slots) :
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (replacementArrays rows repeats p slots direction record) =
      HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (oldArrays rows repeats p slots record) := by
  funext node
  exact OriginalCutBucketReplacement.reconstructRecord_replace_outside
    rows repeats p slots (oldRecord rows repeats p slots record) direction record.2
      node.val node.property

def pairRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (m + 1)) ×
      OriginalExtraCutComparison.Record rows repeats p slots) : PairRecord rows p slots :=
  (HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
      (oldArrays rows repeats p slots sample.2),
    (NodeEmbedding.matrix (oldArrays rows repeats p slots sample.2)
      (WholeArrayInteriorExterior.upperNode p),
    NodeEmbedding.matrix (replacementArrays rows repeats p slots sample.1 sample.2)
      (WholeArrayInteriorExterior.upperNode p)))

theorem pair_totalVariation_le {K : Type*} [Fintype K]
    (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1)))) :
    ((directions.product (OriginalExtraCutComparison.actualLaw rows repeats p slots ν q hbranch)).pushforward
      (pairRecord rows repeats p slots)).totalVariation
      ((directions.product (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
        (pairRecord rows repeats p slots)) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 :=
  OriginalExtraCutComparison.observed_totalVariation_le rows repeats p slots ν q hbranch
    directions (pairRecord rows repeats p slots)

end
end PerfectCompleteness.OriginalCutCollision

end

end OAI
