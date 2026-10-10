import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionArithmetic
import OAI.NumberTheory.Ostmann.Construction.CanonicalLabels

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSupportReduction
open Construction HistorySignedDecode

theorem signedDecode_shape (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) :
    Shape (signedDecode sources seed V l a c) := by
  induction l generalizing a with
  | zero => trivial
  | succ l ih =>
    have hm := decoded_children_match sources seed V l a.toState c ha
    have hp := decoded_children_small_perm sources seed V l a.toState c (Template.matches_length ha)
    simp only [signedDecode,Shape,signedDecode_root]
    refine ⟨assignedSlots_extracted_roles sources _ _ _,?_,trivial,trivial,trivial,trivial,?_,?_,?_,?_⟩
    · exact (List.take_append_drop _ a.small).symm ▸ List.Perm.refl _
    · simpa only [decodeHistory,History.nodeLeft,decodeHistory_root,SignedState.toState] using hp.1
    · simpa only [decodeHistory,History.nodeRight,decodeHistory_root,SignedState.toState] using hp.2
    · apply ih
      simpa only [decodeHistory,History.nodeLeft,decodeHistory_root,SignedState.toState] using hm.1
    · apply ih
      simpa only [decodeHistory,History.nodeRight,decodeHistory_root,SignedState.toState] using hm.2

theorem rebuild_shape {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ) : Shape (rebuild h Xp Xm) := by
  induction h generalizing Xp Xm with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
    simp only [rebuild,Shape,rebuild_root]
    exact ⟨History.supported_compensation_roles hs,
      History.supported_small_split hs,trivial,trivial,trivial,trivial,
      (History.supported_child_small hs).1,(History.supported_child_small hs).2,
      il (History.supported_left hs) _ _,ir (History.supported_right hs) _ _⟩

end Ostmann.Arithmetic.HistorySignedSupportReduction

end

end OAI
