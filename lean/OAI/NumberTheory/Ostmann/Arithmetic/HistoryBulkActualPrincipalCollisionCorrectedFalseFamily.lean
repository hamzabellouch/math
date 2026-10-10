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
attribute [local instance] actualGoodCorrectedFamilyInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime)

theorem correctedFamily_false_eq_sum
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (corrected mixed : Bool) :
    HistoryBulkPatternIntegralReplacement.familyValue (C:=C) (outside:=outside) (l:=l) (p:=p) false
      (correctedFamily (l:=l) C p o outside e he hprime) b corrected mixed hV =
    ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      (selectCorrectedOuterReference (l:=l) C p o outside e i).elim 0 (fun R=>
        (R.rawReference he hprime).weight b mixed *
          (rootDensity (C:=C) (l:=l) (R.frame he hprime) mixed *
            bulkMean (C:=C) (l:=l) (R.frame he hprime) corrected mixed
              (outerNonbulk C l p o) R.permutation hV)) := by
  unfold HistoryBulkPatternIntegralReplacement.familyValue correctedFamily
  rw [sum_extendCommonRootOption]
  apply Finset.sum_congr rfl
  intro i _
  unfold correctedRootFamily
  cases hr : selectCorrectedOuterReference C p o outside e i <;> rfl

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
