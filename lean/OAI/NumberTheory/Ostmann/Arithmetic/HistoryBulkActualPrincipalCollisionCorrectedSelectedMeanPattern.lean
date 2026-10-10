import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedBlockDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSum
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSumDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference HistoryBulkUniversalPatternAggregation
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l) (corrected mixed guarded : Bool)

attribute [local instance] Classical.propDecidable

private theorem selectedMeanPatternProof :
    selectedCollisionMean
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C outside e he hlen hp hV bg corrected mixed guarded =
    patternComplexSum
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (selectedCollisionBlockValue
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C outside e he hlen hp hV bg corrected mixed guarded) :=
  indexCollisionMean_eq_pattern
    (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
    (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
      Internal (Template.initial (2*(bulkSize k L/2)) k) l)
    (κ:=Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) C
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) outside bg.2
    (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
        (p : Pattern (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) (b : Block p → CommonSample (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))=>
      selectedCollisionReferences
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C outside e he hlen hp hV bg i p b)
    (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
        (u : SelectedBulkSample C l) (p : Pattern (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) (b : Block p → CommonSample (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕ Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))=>selectedCollisionMask
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C outside e he hp bg i mixed u p b)
    corrected mixed guarded

theorem selectedCollisionMean_eq_blockPattern :
    selectedCollisionMean
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C outside e he hlen hp hV bg corrected mixed guarded =
    patternComplexSum
      (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
        Internal (Template.initial (2*(bulkSize k L/2)) k) l) C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (selectedCollisionBlockValue
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C outside e he hlen hp hV bg corrected mixed guarded) :=
  selectedMeanPatternProof
    (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
    C outside e he hlen hp hV bg corrected mixed guarded

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
