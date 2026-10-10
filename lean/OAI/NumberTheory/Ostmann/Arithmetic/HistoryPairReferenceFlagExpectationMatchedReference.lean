import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesMatching
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryCompensationRepresentativePatterns HistoryPairSourceLaws HistoryPairSourceCoordinates
open HistoryPairBulkCoordinates
open HistoryPairRows HistoryPairRepresentatives HistoryPairReferenceSourceTransport HistorySymbolicEncoding
attribute [local instance] Classical.propDecidable
local instance matchedReferenceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

structure MatchedBlockReference (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (outside : List ℕ) (l : ℕ) (p : Pattern (pairedHistoryType seed l)) where
  blockDraw : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l))
  valid : ∀i,(expand p blockDraw i).val∈(sources (pairedInternalOrigin seed l i)).candidates
  leftRoot : State
  rightRoot : State
  leftFrequency : FrequencyChoices V l
  rightFrequency : FrequencyChoices V l
  leftMatch : Template.Matches (Template.current seed l) leftRoot.small
  rightMatch : Template.Matches (Template.current seed l) rightRoot.small
  leftSupported : (blockLeftHistory sources seed V l p blockDraw valid leftRoot leftFrequency).Supported V outside
  rightSupported : (blockRightHistory sources seed V l p blockDraw valid rightRoot rightFrequency).Supported V outside
  rootMatching : RootMatching
    (blockLeftHistory sources seed V l p blockDraw valid leftRoot leftFrequency)
    (blockRightHistory sources seed V l p blockDraw valid rightRoot rightFrequency)

namespace MatchedBlockReference
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
    {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}
    (R : MatchedBlockReference sources seed V outside l p)

def left : DecodedDraw sources seed V outside l :=
  blockLeftReference sources seed V l p R.blockDraw R.valid R.leftRoot R.leftFrequency
    R.leftMatch R.leftSupported

def right : DecodedDraw sources seed V outside l :=
  blockRightReference sources seed V l p R.blockDraw R.valid R.rightRoot R.rightFrequency
    R.rightMatch R.rightSupported

def natDraw : BlockDraw p ℕ := natBlockDraw p R.blockDraw Subtype.val Subtype.val_injective

@[simp] theorem left_history : R.left.history=
    blockLeftHistory sources seed V l p R.blockDraw R.valid R.leftRoot R.leftFrequency := rfl

@[simp] theorem right_history : R.right.history=
    blockRightHistory sources seed V l p R.blockDraw R.valid R.rightRoot R.rightFrequency := rfl

@[simp] theorem left_root : R.left.history.root=R.leftRoot :=
  decodeHistory_root sources seed V l R.leftRoot R.left.choices

@[simp] theorem right_root : R.right.history.root=R.rightRoot :=
  decodeHistory_root sources seed V l R.rightRoot R.right.choices

theorem slot_values (i : Internal seed l ⊕ Internal seed l) :
    (slot R.left.history R.right.history (pairedOccurrenceEquiv R.left R.right i)).value=
      expand p R.natDraw i :=
  blockReferences_slot_values sources seed V l p R.blockDraw R.valid
    R.leftRoot R.rightRoot R.leftFrequency R.rightFrequency R.leftMatch R.rightMatch
    R.leftSupported R.rightSupported i

def root_matching : RootMatching R.left.history R.right.history := R.rootMatching

theorem left_labels : TreeSourceLabels seed R.left.history := R.left.labels

theorem right_labels : TreeSourceLabels seed R.right.history := R.right.labels

end MatchedBlockReference
end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
