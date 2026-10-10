import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionOptionRealBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionTerm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkActualCorrectedPrincipalBlockFamily
open HistoryBulkActualPrincipalCollision HistoryBulkPrincipalCollisionError
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀ q ∈ outside, q.Prime)
  (hV : ∀ q ∈ outside, ∀ j ≤ l, frequencyBound Bs BD Bz k L j < q)

theorem correctedKernelOptionProof
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (o : OriginalOuter (fun _ => C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) :
    (selectedBulkPrior C l).cmean (fun sample =>
      (selectCorrectedOuterReference (l:=l) C p o outside e i).elim 0
        (fun corrected => corrected.kernelTerm (l:=l) he hlen hp hV true sample)) =
      ((selectCorrectedOuterReference (l:=l) C p o outside e i).map
        (fun corrected => corrected.collisionReference (l:=l) he hlen hp hV)).elim 0
        (fun reference => referenceKernel C
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          outside (outerNonbulk C l p o) reference (outerBlocks C l p o) true *
          (selectedBulkPrior C l).cmean (fun sample =>
            (((selectCorrectedOuterReference (l:=l) C p o outside e i).elim 0
              (fun corrected => density (corrected.frame (l:=l) he hp) true) : ℝ) : ℂ) *
              (open scoped Classical in
                if true ∧ ¬fibreSmallOutsideGuard C outside (outerNonbulk C l p o) sample
                then 0 else reference.value true true sample))) :=
  cmean_option_real_scale
    (Ω := SelectedBulkSample C l)
    (α := CorrectedSelectedOuter (l:=l) C p o outside e i)
    (β := PrincipalCollisionReference (l:=l) C outside (outerNonbulk C l p o) p)
    (selectedBulkPrior C l)
    (selectCorrectedOuterReference (l:=l) C p o outside e i)
    (fun R => R.collisionReference (l:=l) he hlen hp hV)
    (fun R u => R.kernelTerm (l:=l) he hlen hp hV true u)
    (fun r => referenceKernel C
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      outside (outerNonbulk C l p o) r (outerBlocks C l p o) true)
    (fun R => density (R.frame (l:=l) he hp) true)
    (fun r u => (open scoped Classical in
      if true ∧ ¬fibreSmallOutsideGuard C outside (outerNonbulk C l p o) u then 0 else r.value true true u))
    (fun R u => R.kernelTerm_true_eq_collision (l:=l) he hlen hp hV u)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
