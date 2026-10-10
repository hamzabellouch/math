import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction

theorem signedDecode_toHistory_of_nonnegative
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (hn : (signedDecode sources seed V l a c).Nonnegative) :
    (signedDecode sources seed V l a c).toHistory=decodeHistory sources seed V l a.toState c := by
  induction l generalizing a with
  | zero => rfl
  | succ l ih =>
    have ha : a.Nonnegative := hn.1
    have hl := hn.2.2.1
    have hr := hn.2.2.2
    simp only [signedDecode,SignedHistory.toHistory,decodeHistory]
    rw [← signedPivot_toNat a ha]
    congr 1
    · exact ih _ c.2.2.2.1 hl
    · exact ih _ c.2.2.2.2 hr

theorem signedDecode_ofState_toHistory
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (hn : (signedDecode sources seed V l (SignedState.ofState a) c).Nonnegative) :
    (signedDecode sources seed V l (SignedState.ofState a) c).toHistory=decodeHistory sources seed V l a c := by
  simpa only [SignedState.toState_ofState] using
    signedDecode_toHistory_of_nonnegative sources seed V l (SignedState.ofState a) c hn

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
