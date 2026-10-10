import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedGuard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionExpand
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionKernel
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionScalar

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
open HistoryBulkActualPrincipalCollision
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
  (R : CorrectedSelectedOuter (l:=l) C p o outside e i)
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem kernelTerm_true_eq_collision (u : SelectedBulkSample C l) :
    R.kernelTerm he hlen hp hV true u =
      referenceKernel C
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        outside (outerNonbulk C l p o) (R.collisionReference he hlen hp hV)
        (outerBlocks C l p o) true *
      ((density (R.frame he hp) true:ℂ)*
        (if true ∧ ¬fibreSmallOutsideGuard C outside (outerNonbulk C l p o) u then 0 else
          (R.collisionReference he hlen hp hV).value true true u)) :=
  (R.kernelTerm_true_factors he hlen hp hV u).trans
    (HistoryBulkActualPrincipalKernelStageCorrected.guarded_kernel_scalar _ _ _ _ _ _ _ _
      (R.kernel_staticPairMask_eq_guard he hp u)
      (R.density_true_eq_extractedDensity he hp).symm
      (R.collisionReference_value_eq he hlen hp hV u).symm
      (R.kernelProduct_true_eq_referenceKernel he hlen hp hV u))

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal.CorrectedSelectedOuter

end

end OAI
