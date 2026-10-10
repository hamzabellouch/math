import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedKernel
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedOption

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryPairPattern HistoryDiagonalRemainingRootMatching
open HistoryBulkFibreGiantApproximation HistoryBulkActualCorrectedPrincipalBlockFamily
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreSourceMean
open HistoryBulkPrincipalCollisionError HistoryBulkActualPrincipalValueFrame
open HistoryBulkActualPrincipalValueFrameMatched HistoryBulkFibreOriginalReference
open HistoryBulkActualPrincipalCollision
attribute [local instance] Classical.propDecidable actualGoodCorrectedFamilyInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (outside : List ℕ)(e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem correctedOption_false
    (O : Option (CorrectedSelectedOuter C p o outside e i))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (corrected mixed : Bool) :
    (O.map (fun reference=>reference.collisionReference he hlen hp hV)).elim 0
      (fun reference=>referenceKernel (l:=l)
        (ι := Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l)
        C (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        outside (outerNonbulk C l p o) reference b mixed *
        (selectedBulkPrior C l).cmean (fun sample=>
          ((O.elim 0 (fun selected=>density (C:=C) (l:=l) (selected.frame he hp) mixed):ℝ):ℂ) *
          (if false ∧ ¬fibreSmallOutsideGuard C outside (outerNonbulk C l p o) sample
            then 0 else reference.value corrected mixed sample))) =
      O.elim 0 (fun reference=>(reference.rawReference he hp).weight b mixed *
        (rootDensity (C:=C) (l:=l) (reference.frame he hp) mixed *
          bulkMean (C:=C) (l:=l) (reference.frame he hp) corrected mixed
            (outerNonbulk C l p o) reference.permutation hV)) :=
  option_kernel_mean_false
    (α := CorrectedSelectedOuter C p o outside e i)
    (β := PrincipalCollisionReference (l:=l)
      (ι := Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) C outside (outerNonbulk C l p o) p)
    (Ω := SelectedBulkSample C l)
    (selectedBulkPrior C l).cmean O
    (fun R=>R.collisionReference he hlen hp hV)
    (fun R=>density (C:=C) (l:=l) (R.frame he hp) mixed)
    (fun r=>referenceKernel (l:=l)
      (ι := Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l)
      C (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      outside (outerNonbulk C l p o) r b mixed)
    (fun r u=>r.value corrected mixed u)
    (fun u=>¬fibreSmallOutsideGuard C outside (outerNonbulk C l p o) u)
    (fun R=>(R.rawReference he hp).weight b mixed *
      (rootDensity (C:=C) (l:=l) (R.frame he hp) mixed *
        bulkMean (C:=C) (l:=l) (R.frame he hp) corrected mixed
          (outerNonbulk C l p o) R.permutation hV))
    (fun R=>R.collisionReference_weighted_cmean he hlen hp hV b corrected mixed)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
