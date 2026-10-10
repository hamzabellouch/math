import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedGuard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedValue
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
open HistoryBulkFibreGiantApproximation HistoryBulkPrincipalCollisionError
open HistoryBulkReferencePeriodicMeanSource HistorySignedResidueFactorization
open HistoryBulkActualCorrectedPrincipalBlockFamily
local instance correctedKernelCollisionScalarInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
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

theorem kernel_staticPairMask_eq_guard (u : SelectedBulkSample C l) :
    staticPairMask
      ((R.frame he hp).newLeft (fibreAssignment C (outerNonbulk C l p o) u))
      ((R.frame he hp).newRight (R.squareRightSource he u)) outside=
    guardIndicator (fibreSmallOutsideGuard C outside (outerNonbulk C l p o) u) :=
  R.collisionReference_static_guard he hp u

theorem collisionReference_value_eq (u : SelectedBulkSample C l) :
    (R.collisionReference he hlen hp hV).value true true u=
      (principalData R he (bulkSize k L/2) hlen hp hV).value true true u :=
  R.collisionReference_value he hlen hp hV true true u

theorem density_true_eq_extractedDensity :
    (density (R.frame he hp) true : ℂ)=
      Frame.extractedDensity (C:=C) (R.frame he hp).leftSource :=
  density_cast (R.frame he hp) true

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal.CorrectedSelectedOuter

end

end OAI
