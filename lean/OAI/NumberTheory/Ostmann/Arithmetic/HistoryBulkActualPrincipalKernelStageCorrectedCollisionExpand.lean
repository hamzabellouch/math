import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal.CorrectedSelectedOuter
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkFibreOriginalReference
open HistoryBulkFibreGiantApproximation
open HistoryBulkReferencePeriodicMeanSource HistorySignedResidueFactorization
open HistoryBulkActualCorrectedPrincipalBlockFamily
attribute [local instance] Classical.propDecidable
attribute [local instance] correctedKernelStageValueInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
  (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem kernelTerm_true_factors (u : SelectedBulkSample C l) :
    R.kernelTerm he hlen hp hV true u =
    staticPairMask
      ((R.frame he hp).newLeft (fibreAssignment C (outerNonbulk C l p o) u))
      ((R.frame he hp).newRight (R.squareRightSource he u)) outside *
      (Frame.extractedDensity (C:=C) (R.frame he hp).leftSource *
        ((principalData R he (bulkSize k L/2) hlen hp hV).value true true u *
          (R.kernelProduct he hp true u:ℂ))) := rfl

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal.CorrectedSelectedOuter

end

end OAI
