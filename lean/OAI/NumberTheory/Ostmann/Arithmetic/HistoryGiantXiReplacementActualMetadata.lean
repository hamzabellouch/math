import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBounds
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencySupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistoryGiantReferenceSourceBounds HistorySignedXiTransport HistoryGiantReferenceMean

theorem decoded_shared_giants (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (P Q : ℤ) :
    RootGiantsAgree (decodeHistory sources seed V l (giantState a P Q) c)
      (decodeHistory sources seed V l (giantState b P Q) e) := by
  simp only [RootGiantsAgree,decodeHistory_root,giantState,and_self]

theorem assigned_giant_tree_source_labels (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (x : SourceAssignment sources (Template.current seed l))
    (s P Q : ℤ) (c : HistoryChoices sources seed V l) :
    TreeSourceLabels seed (decodeHistory sources seed V l
      (giantState (sourceState sources (Template.current seed l) x s) P Q) c) :=
  decoded_tree_source_labels sources seed V l _ c (Template.assignedSlots_matches sources _ x)

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
