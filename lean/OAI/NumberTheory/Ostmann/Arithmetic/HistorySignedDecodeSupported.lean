import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeAgreement

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction

theorem SignedState.giants_pos_of_toState_positive (a : SignedState)
    (ha : a.toState.Positive) : 0 < a.giantPlus ∧ 0 < a.giantMinus := by
  have hp : 0 < a.giantPlus.toNat := ha _ (by simp [State.values, SignedState.toState])
  have hm : 0 < a.giantMinus.toNat := ha _ (by simp [State.values, SignedState.toState])
  constructor <;> omega

theorem signedDecode_nonnegative_of_supported
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a.toState c).Supported V outside) :
    (signedDecode sources seed V l a c).Nonnegative := by
  induction l generalizing a with
  | zero =>
    have hp := a.giants_pos_of_toState_positive (History.supported_root_positive hs)
    exact ⟨hp.1.le, hp.2.le⟩
  | succ l ih =>
    have haroot := History.supported_root_positive hs
    rw [decodeHistory_root] at haroot
    have ha : a.Nonnegative :=
      ⟨(a.giants_pos_of_toState_positive haroot).1.le,
        (a.giants_pos_of_toState_positive haroot).2.le⟩
    let T := Template.current seed l
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    let n := (Template.remainder (l+1) T).length
    let hp := a.small.take n
    let hm := a.small.drop n
    let p := signedPivot a c.1.val c.2.1.val u hp hm
    have hpnat : 0 < decodedPivot a.toState c.1.val c.2.1.val u hp hm :=
      History.supported_pivot_pos hs
    have hcast : p.toNat = decodedPivot a.toState c.1.val c.2.1.val u hp hm :=
      signedPivot_toNat a ha _ _ _ _ _
    have hp0 : 0 < p := by omega
    change a.Nonnegative ∧ 0 ≤ p ∧
      (signedDecode sources seed V l
        ⟨c.1.val, p, a.giantPlus, Template.reinsert (l+1) T u hp⟩ c.2.2.2.1).Nonnegative ∧
      (signedDecode sources seed V l
        ⟨c.2.1.val, p, a.giantMinus, Template.reinsert (l+1) T u hm⟩ c.2.2.2.2).Nonnegative
    refine ⟨ha, hp0.le, ?_, ?_⟩
    · apply ih
      · simpa only [SignedState.toState, hcast] using History.supported_left hs
    · apply ih
      · simpa only [SignedState.toState, hcast] using History.supported_right hs

theorem signedDecode_toHistory_of_supported
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a.toState c).Supported V outside) :
    (signedDecode sources seed V l a c).toHistory =
      decodeHistory sources seed V l a.toState c :=
  signedDecode_toHistory_of_nonnegative sources seed V l a c
    (signedDecode_nonnegative_of_supported sources seed V l a c outside hs)

theorem signedDecode_ofState_nonnegative_of_supported
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) :
    (signedDecode sources seed V l (SignedState.ofState a) c).Nonnegative :=
  signedDecode_nonnegative_of_supported sources seed V l (SignedState.ofState a) c outside
    (by simpa only [SignedState.toState_ofState] using hs)

theorem signedDecode_ofState_toHistory_of_supported
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) :
    (signedDecode sources seed V l (SignedState.ofState a) c).toHistory =
      decodeHistory sources seed V l a c :=
  signedDecode_ofState_toHistory sources seed V l a c
    (signedDecode_ofState_nonnegative_of_supported sources seed V l a c outside hs)

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
