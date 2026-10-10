import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction Construction.CanonicalOccurrenceTransport HistoryPairBulkTransport HistoryPairBulkCoordinates

def assignedRootMatching (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (s t : ℤ) (gp gm qp qm : ℕ)
    (x y : SourceAssignment sources (Template.current seed l))
    (c d : HistoryChoices sources seed V l)
    (π : Equiv.Perm (Fin (Template.current seed l).length))
    (hvalues : ∀i, (y i).val = (x (π i)).val)
    (hbulk : ∀i, ((Template.current seed l).get i).role = .bulk ↔
      ((Template.current seed l).get (π i)).role = .bulk) :
    RootMatching (assignedHistory sources seed V l s gp gm x c)
      (assignedHistory sources seed V l t qp qm y d) :=
  matching_of_assignments sources _ _ _
    (root_matches (assignedLabels sources seed V l s gp gm x c))
    (root_matches (assignedLabels sources seed V l t qp qm y d)) x y
    (by simp only [assignedHistory,decodeHistory_root,assignedRoot])
    (by simp only [assignedHistory,decodeHistory_root,assignedRoot]) π hvalues hbulk

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
