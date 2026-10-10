import OAI.NumberTheory.Ostmann.Construction.CanonicalFrame
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesDefs

namespace OAI

noncomputable section
namespace Ostmann.Construction
open CanonicalOccurrenceTransport Arithmetic.HistoryOccurrenceVariables

theorem decoded_internalSlot_eq_historyDraw (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) (i : Internal seed l) :
    (internalSlot (decodeHistory sources seed V l a c)
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l a c ha) i)).value =
      (historyDraws sources seed V l c i).val := by
  induction l generalizing a with
  | zero => exact Empty.elim i
  | succ l ih =>
    have hc := decoded_children_match sources seed V l a c ha
    let f := canonicalFrame sources seed V l a c.1 c.2.1 c.2.2.1
    have hleft : Template.Matches (Template.current seed l) f.plusState.small := by
      simpa only [f,canonicalFrame,decodeHistory,History.nodeLeft,decodeHistory_root] using hc.1
    have hright : Template.Matches (Template.current seed l) f.minusState.small := by
      simpa only [f,canonicalFrame,decodeHistory,History.nodeRight,decodeHistory_root] using hc.2
    rcases i with i | i | i
    · simp only [decodeHistory,internalEquiv,internalSlot,historyDraws]
      change ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l))
        c.2.2.1).get (finCongr (assignedSlots_length _ _ _).symm i)).value = (c.2.2.1 i).val
      simp [assignedSlots, Template.sample]
      rfl
    · exact ih f.plusState c.2.2.2.1 hleft i
    · exact ih f.minusState c.2.2.2.2 hright i

theorem decoded_coordinateSample_internal (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) (i : Internal seed l) :
    coordinateSample seed (decodeHistory sources seed V l a c)
      (decoded_tree_source_labels sources seed V l a c ha) (.inr (.inr i)) =
      ((historyDraws sources seed V l c i).val:ℤ) := by
  change ((internalSlot (decodeHistory sources seed V l a c)
      (internalEquiv seed _ (decoded_tree_source_labels sources seed V l a c ha) i)).value:ℤ)=_
  exact_mod_cast decoded_internalSlot_eq_historyDraw sources seed V l a c ha i

end Ostmann.Construction

end

end OAI
