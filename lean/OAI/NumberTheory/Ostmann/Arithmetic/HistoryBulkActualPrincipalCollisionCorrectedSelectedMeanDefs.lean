import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackgroundDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMask
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedReferences
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSumDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkPrincipalCollisionError HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l)

attribute [local instance] Classical.propDecidable

def selectedCollisionMean (corrected mixed guarded : Bool) : ℂ :=
  indexCollisionMean
    (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
    (ι:=Internal (Template.initial (2*(bulkSize k L/2)) k) l ⊕
      Internal (Template.initial (2*(bulkSize k L/2)) k) l)
    (κ:=Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) C
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) outside bg.2
    (fun i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)=>
      selectedCollisionReferences
        (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
        C outside e he hlen hp hV bg i)
    (fun i=>selectedCollisionMask
      (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
      C outside e he hp bg i mixed)
    corrected mixed guarded

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
