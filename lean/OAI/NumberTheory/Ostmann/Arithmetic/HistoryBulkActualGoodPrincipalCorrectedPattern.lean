import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkPrincipalSourceReindex
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkGoodPatternPrincipalFrame
open HistoryPairKernelReplacement
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance actualGoodCorrectedPatternInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime)
  (hgood : ¬TransferBadArrangement
    (DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e))

theorem correctedReference_value
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (R : CorrectedSelectedOuter C p o outside e i)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    (R.rawReference he hprime).weight b true *
      (rootDensity (R.frame he hprime) true *
        principalOperator (R.frame he hprime) true true R.permutation hV)=
    (R.goodReference he hprime hgood (density (R.frame he hprime) true)
      (density_mem (R.frame he hprime) true)).weight b true *
        principalOperator (R.frame he hprime) true true R.permutation hV := by
  let K : ℝ := ∏q : Block p,symbolicKernel true (R.frame he hprime).left
    (R.frame he hprime).right (R.frame he hprime).left_supported
    (R.frame he hprime).right_supported (R.representative he hprime q) (b q).val
  change ((1*K : ℝ):ℂ) * (rootDensity (R.frame he hprime) true *
      principalOperator (R.frame he hprime) true true R.permutation hV)=
    ((density (R.frame he hprime) true*K : ℝ):ℂ) *
      principalOperator (R.frame he hprime) true true R.permutation hV
  rw [one_mul,Complex.ofReal_mul,density_cast]
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

theorem familyValue_correctedFamily
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    HistoryBulkPatternIntegralReplacement.familyValue true
      (correctedFamily C p o outside e he hprime) b true true hV=
    HistoryBulkGoodPatternAggregation.familyValue
      (correctedGoodFamily C p o outside e he hprime hgood) b true true hV := by
  unfold HistoryBulkPatternIntegralReplacement.familyValue
    HistoryBulkGoodPatternAggregation.familyValue correctedFamily correctedGoodFamily
  rw [sum_extendCommonRootOption,sum_extendCommonRootOption]
  apply Finset.sum_congr rfl
  intro i _
  unfold correctedRootFamily correctedGoodRootFamily
  cases hr : selectCorrectedOuterReference C p o outside e i with
  | none => rfl
  | some R =>
    exact correctedReference_value C p o outside e he hprime hgood i R b hV

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
