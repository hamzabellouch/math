import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMaskBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSelectedReferences
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSum

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
attribute [local instance] Classical.propDecidable
local instance correctedSelectedCollisionDefsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
