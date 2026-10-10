import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeSupported

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction

theorem signedDecode_positiveIntegral_of_supported
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a.toState c).Supported V outside) :
    (signedDecode sources seed V l a c).PositiveIntegral := by
  induction l generalizing a with
  | zero =>
    exact a.giants_pos_of_toState_positive (History.supported_root_positive hs)
  | succ l ih =>
    have haroot := History.supported_root_positive hs
    rw [decodeHistory_root] at haroot
    have ha := a.giants_pos_of_toState_positive haroot
    let T := Template.current seed l
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    let n := (Template.remainder (l+1) T).length
    let hp := a.small.take n
    let hm := a.small.drop n
    let p := signedPivot a c.1.val c.2.1.val u hp hm
    have hcast : p.toNat=decodedPivot a.toState c.1.val c.2.1.val u hp hm :=
      signedPivot_toNat a ⟨ha.1.le,ha.2.le⟩ _ _ _ _ _
    have hpnat : 0<decodedPivot a.toState c.1.val c.2.1.val u hp hm :=
      History.supported_pivot_pos hs
    have hp0 : 0<p := by omega
    have hfreq : a.frequency≠0 := History.supported_root_frequency_ne_zero hs
    have hupos : 0<(u.map SmallSlot.value).prod := History.supported_compensation_product_pos hs
    have hu0 : ((u.map SmallSlot.value).prod:ℤ)≠0 := by exact_mod_cast hupos.ne'
    have hrev := History.supported_reversal hs
    simp only [decodeHistory_root,SignedState.toState,Nat.cast_mul,
      Int.toNat_of_nonneg ha.1.le,Int.toNat_of_nonneg ha.2.le] at hrev
    change (0<a.giantPlus ∧ 0<a.giantMinus) ∧ 0<p ∧
      a.frequency*((u.map SmallSlot.value).prod:ℤ)≠0 ∧
      a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣
        reversalNumerator _ _ (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
          (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) ∧ _ ∧ _
    refine ⟨ha,hp0,mul_ne_zero hfreq hu0,?_,?_,?_⟩
    · simp only [signedDecode_root]
      exact ⟨(decodedPivot a.toState c.1.val c.2.1.val u hp hm:ℤ),hrev⟩
    · apply ih
      simp only [SignedState.toState]
      rw [signedPivot_toNat a ⟨ha.1.le,ha.2.le⟩]
      exact History.supported_left hs
    · apply ih
      simp only [SignedState.toState]
      rw [signedPivot_toNat a ⟨ha.1.le,ha.2.le⟩]
      exact History.supported_right hs

theorem signedDecode_ofState_positiveIntegral_of_supported
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (hs : (decodeHistory sources seed V l a c).Supported V outside) :
    (signedDecode sources seed V l (SignedState.ofState a) c).PositiveIntegral :=
  signedDecode_positiveIntegral_of_supported sources seed V l (SignedState.ofState a) c outside
    (by simpa only [SignedState.toState_ofState] using hs)

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
