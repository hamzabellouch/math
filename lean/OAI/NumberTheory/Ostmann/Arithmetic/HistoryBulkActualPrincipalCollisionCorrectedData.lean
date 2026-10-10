import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameMatchedCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorReferences
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportBlocks

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkPrincipalCollisionError
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable
local instance correctedCollisionDataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l p}
  (P : MatchedPrincipalReferenceData C R) (a : SelectedNonbulkSample C l)
  (u₀ : SelectedBulkSample C l)
  (hsmall : R.left.history.root.small=assignedSlots C.sources (SelectedTemplate k L l)
    (fibreAssignment C a u₀))

def fromMatchedData : PrincipalCollisionReference C outside a p where
  amplitude := P.amplitude u₀
  referenceBulk := u₀
  leftSmall := hsmall
  representative := (typedBlockEquiv R.left R.right p R.natDraw R.slot_values).symm
  residues := fun u => (P.amplitude u).residue

@[simp] theorem fromMatchedData_amplitudeAt (u : SelectedBulkSample C l) :
    (fromMatchedData P a u₀ hsmall).amplitudeAt u=P.amplitude u := rfl

theorem fromMatchedData_value (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    (fromMatchedData P a u₀ hsmall).value corrected mixed u=P.value corrected mixed u := rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
