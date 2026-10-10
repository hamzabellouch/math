import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternAggregationFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexFrequency

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkPrincipalSourceReindex
attribute [local instance] Classical.propDecidable
local instance actualGoodCorrectedFamilyInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

def CorrectedSelectedOuter.rawReference (R : CorrectedSelectedOuter C p o outside e i)
    (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime) :
    HistoryBulkPatternIntegralReplacement.Reference C outside l p where
  frame := R.frame he hprime
  nonbulk := outerNonbulk C l p o
  permutation := R.permutation
  representative := R.representative he hprime
  mask := 1
  mask_mem := ⟨zero_le_one,le_rfl⟩

variable (C p o outside e)
  (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime)

def correctedRootFamily
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    Option (HistoryBulkPatternIntegralReplacement.Reference C outside l p) :=
  (selectCorrectedOuterReference C p o outside e i).map (fun R=>R.rawReference he hprime)

def correctedFamily : HistoryBulkPatternIntegralReplacement.Family C outside l p :=
  extendCommonRootOption (frequencyBound Bs BD Bz k L) l
    (correctedRootFamily C p o outside e he hprime)

variable (hgood : ¬TransferBadArrangement
  (DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e))

def correctedGoodRootFamily
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) :
    Option (HistoryBulkGoodPatternAggregation.Reference C outside l p) :=
  (selectCorrectedOuterReference C p o outside e i).map (fun R=>
    R.goodReference he hprime hgood (density (R.frame he hprime) true)
      (density_mem (R.frame he hprime) true))

def correctedGoodFamily : HistoryBulkGoodPatternAggregation.Family C outside l p :=
  extendCommonRootOption (frequencyBound Bs BD Bz k L) l
    (correctedGoodRootFamily C p o outside e he hprime hgood)

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
