import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionNormalForm
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedCollisionOptionProof

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkActualCorrectedPrincipalBlockFamily
open HistoryBulkActualPrincipalCollision HistoryBulkActualPrincipalCollisionCorrected
open HistoryBulkPrincipalCollisionError
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
      (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem correctedKernelFrequencySumProof
    (bg : Background C l)
    (b : Block p → CommonSample
      (ι := Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    let outer := restoreOuterBackground C l p bg b
    (∑ index : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      (selectedBulkPrior C l).cmean (fun sample =>
        (selectCorrectedOuterReference (l:=l) C p outer outside e index).elim 0
          (fun corrected => corrected.kernelTerm (l:=l) he hlen hprime hV true sample))) =
      ∑ index : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
        ((selectCorrectedOuterReference (l:=l) C p outer outside e index).map
          (fun corrected => corrected.collisionReference (l:=l) he hlen hprime hV)).elim 0
          (fun reference => referenceKernel C
            (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
            (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
            outside (outerNonbulk C l p outer) reference (outerBlocks C l p outer) true *
            (selectedBulkPrior C l).cmean (fun sample =>
              (((selectCorrectedOuterReference (l:=l) C p outer outside e index).elim 0
                (fun corrected => density (corrected.frame (l:=l) he hprime) true) : ℝ) : ℂ) *
                (open scoped Classical in
                  if true ∧ ¬fibreSmallOutsideGuard C outside (outerNonbulk C l p outer) sample
                  then 0 else reference.value true true sample))) :=
  Finset.sum_congr (M:=ℂ)
    (rfl : (Finset.univ : Finset (Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))) = Finset.univ)
    (fun i _ => correctedKernelOptionProof
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C p outside e he hlen hprime hV i (restoreOuterBackground C l p bg b))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
