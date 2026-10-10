import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLabels
import OAI.NumberTheory.Ostmann.Construction.CanonicalLabels

namespace OAI

noncomputable section
namespace Ostmann.Construction
open Ostmann.Arithmetic.HistorySymbolicEncoding

theorem decoded_tree_source_labels (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) :
    TreeSourceLabels seed (decodeHistory sources seed V l a c) := by
  induction l generalizing a with
  | zero => exact ha
  | succ l ih =>
    have hh := Template.matches_halves
      (Template.remainder (l+1) (Template.current seed l)) a.small ha
    have hu := Template.assignedSlots_matches sources
      (Template.extracted (l+1) (Template.current seed l)) c.2.2.1
    have hc := decoded_children_match sources seed V l a c ha
    rw [decodeHistory,TreeSourceLabels]
    refine ⟨ha,hh.1,hh.2,hu,?_,?_⟩
    · exact ih _ c.2.2.2.1 (by
        simpa only [decodeHistory,History.nodeLeft,decodeHistory_root] using hc.1)
    · exact ih _ c.2.2.2.2 (by
        simpa only [decodeHistory,History.nodeRight,decodeHistory_root] using hc.2)

end Ostmann.Construction

end

end OAI
