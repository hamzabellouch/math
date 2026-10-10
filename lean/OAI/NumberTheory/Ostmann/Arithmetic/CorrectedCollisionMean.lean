import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMeanPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollision
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCollisionMeanExchange
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanScalarDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

section
noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkUniversalPatternAggregation
open HistoryBulkActualPrincipalCollisionCorrected
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
      (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

attribute [local instance] Classical.propDecidable

private theorem selectedKernelCollisionMeanProof :
    (∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑p : Pattern (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C p outside e he hlen hprime hV
          i.1 i.2.1 i.2.2 true) =
    (backgroundPrior C l).cmean (fun bg=>
      selectedCollisionMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C outside e he hlen hprime hV bg true true true) :=
  (sum_selectedKernelMean_eq_backgroundIndex (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C outside e he hlen hprime hV).trans
    (congrArg (backgroundPrior C l).cmean
      (funext (fun bg=>
        (congrArg (patternComplexSum (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
          (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
          (funext (fun p=>funext (fun b=>
            sum_selectedKernelOptionValue_eq_collisionBlock (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
              C p outside e he hlen hprime hV bg b)))).trans
          (selectedCollisionMean_eq_blockPattern
            (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
            C outside e he hlen hprime hV bg true true true).symm)))

private theorem selectedKernelCollisionMeanComplete :
    (∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑p : Pattern (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C p outside e he hlen hprime hV
          i.1 i.2.1 i.2.2 true) =
    (backgroundPrior C l).cmean (fun bg=>
      selectedCollisionMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C outside e he hlen hprime hV bg true true true) :=
  selectedKernelCollisionMeanProof (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C outside e he hlen hprime hV

public theorem sum_selectedKernelMean_eq_collisionMean :
    (∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑p : Pattern (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C p outside e he hlen hprime hV
          i.1 i.2.1 i.2.2 true) =
    (backgroundPrior C l).cmean (fun bg=>
      selectedCollisionMean (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C outside e he hlen hprime hV bg true true true) :=
  selectedKernelCollisionMeanComplete (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C outside e he hlen hprime hV

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
end
end

end OAI
