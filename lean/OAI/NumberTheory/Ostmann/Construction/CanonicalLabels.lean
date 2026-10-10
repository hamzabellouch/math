import OAI.NumberTheory.Ostmann.Construction.CanonicalNode
import OAI.NumberTheory.Ostmann.Construction.TemplateLabels

namespace OAI

noncomputable section
namespace Ostmann.Construction

theorem decoded_children_match (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V (l+1))
    (ha : Template.Matches (Template.current seed (l+1)) a.small) :
    Template.Matches (Template.current seed l)
      (History.nodeLeft (decodeHistory sources seed V (l+1) a c)).root.small ∧
    Template.Matches (Template.current seed l)
      (History.nodeRight (decodeHistory sources seed V (l+1) a c)).root.small := by
  let T := Template.current seed l
  have hh := Template.matches_halves (Template.remainder (l+1) T) a.small ha
  have hu := Template.assignedSlots_matches sources (Template.extracted (l+1) T) c.2.2.1
  constructor
  · simpa only [decodeHistory,History.nodeLeft,decodeHistory_root,T] using
      Template.reinsert_matches (l+1) T _ _ hu hh.1
  · simpa only [decodeHistory,History.nodeRight,decodeHistory_root,T] using
      Template.reinsert_matches (l+1) T _ _ hu hh.2

theorem decoded_leaf_matches (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) :
    ∀ b∈(decodeHistory sources seed V l a c).leafStates, Template.Matches seed b.small := by
  induction l generalizing a with
  | zero =>
    intro b hb
    have hb' : b=a := by simpa only [decodeHistory,History.leafStates,List.mem_singleton] using hb
    subst b
    exact ha
  | succ l ih =>
    have hh := decoded_children_match sources seed V l a c ha
    intro b hb
    have hb' := List.mem_append.mp hb
    rcases hb' with hb' | hb'
    · exact ih _ c.2.2.2.1 hh.1 b (by
        simpa only [decodeHistory,History.nodeLeft,decodeHistory_root] using hb')
    · exact ih _ c.2.2.2.2 hh.2 b (by
        simpa only [decodeHistory,History.nodeRight,decodeHistory_root] using hb')

end Ostmann.Construction

end

end OAI
