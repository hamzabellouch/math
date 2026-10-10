import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedOption
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedBlockDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedNormalForm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
open HistoryBulkActualPrincipalCollision HistoryBulkIndependentFibreReference
open HistoryBulkUniversalPatternAggregation HistoryBulkPrincipalSourceReindex
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable correctedSelectedCollisionDefsInternalDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l)

theorem selectedCollisionMean_eq_pattern (corrected mixed guarded : Bool) :
    selectedCollisionMean (l:=l) C outside e he hlen hp hV bg
      corrected mixed guarded =
    patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (selectedCollisionBlockValue (l:=l) C outside e he hlen hp hV bg corrected mixed guarded) :=
  indexCollisionMean_eq_pattern (l:=l)
    (ι := Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l)
    (κ := Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) C
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) outside bg.2
    (fun i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)=>
      selectedCollisionReferences (l:=l) C outside e he hlen hp hV bg i)
    (fun i=>selectedCollisionMask (l:=l) C outside e he hp bg i mixed)
    corrected mixed guarded

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
