import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceTree

namespace OAI

namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction

def TreeSourceLabels (seed : List SourceSlot) : {l : ℕ} → History l → Prop
  | _, .leaf a => Template.Matches seed a.small
  | l+1, .node a _ u hp hm left right =>
      Template.Matches (Template.current seed (l+1)) a.small ∧
      Template.Matches (Template.remainder (l+1) (Template.current seed l)) hp ∧
      Template.Matches (Template.remainder (l+1) (Template.current seed l)) hm ∧
      Template.Matches (Template.extracted (l+1) (Template.current seed l)) u ∧
      TreeSourceLabels seed left ∧ TreeSourceLabels seed right

theorem TreeSourceLabels.leaves {seed : List SourceSlot} {l : ℕ} {h : History l}
    (hh : TreeSourceLabels seed h) :
    ∀ a ∈ h.leafStates, Template.Matches seed a.small := by
  induction h with
  | leaf a =>
    intro b hb
    have he : b=a := by simpa only [History.leafStates,List.mem_singleton] using hb
    subst b
    exact hh
  | node a p u hp hm left right il ir =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact il hh.2.2.2.2.1 b hb
    · exact ir hh.2.2.2.2.2 b hb

end Ostmann.Arithmetic.HistorySymbolicEncoding

end OAI
