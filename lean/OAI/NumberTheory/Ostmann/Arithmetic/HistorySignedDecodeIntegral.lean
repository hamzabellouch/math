import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeAgreement
import OAI.NumberTheory.Ostmann.Arithmetic.LinearReversal

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction

def SignedHistory.PositiveIntegral : {l : ℕ} → SignedHistory l → Prop
  | _,.leaf a => 0<a.giantPlus ∧ 0<a.giantMinus
  | _,.node a p u hp hm left right =>
    (0<a.giantPlus ∧ 0<a.giantMinus) ∧ 0<p ∧
      a.frequency*((u.map SmallSlot.value).prod:ℤ)≠0 ∧
      a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣
        reversalNumerator left.root.frequency right.root.frequency
          (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
          (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) ∧
      left.PositiveIntegral ∧ right.PositiveIntegral

theorem SignedHistory.PositiveIntegral.nonnegative {l : ℕ} {h : SignedHistory l}
    (hp : h.PositiveIntegral) : h.Nonnegative := by
  induction h with
  | leaf a => exact ⟨hp.1.le,hp.2.le⟩
  | node a p u hplus hminus left right il ir =>
    exact ⟨⟨hp.1.1.le,hp.1.2.le⟩,hp.2.1.le,il hp.2.2.2.2.1,ir hp.2.2.2.2.2⟩

theorem signedPivot_reversal (a : SignedState) (v w : ℤ) (u hp hm : List SmallSlot)
    (hd : a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣
      reversalNumerator v w (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
        (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ))) :
    reversalNumerator v w (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ))=
      a.frequency*((u.map SmallSlot.value).prod:ℤ)*signedPivot a v w u hp hm := by
  dsimp only [signedPivot]
  simpa only [mul_comm] using (Int.ediv_mul_cancel hd).symm

theorem signedPivot_real_eq (a : SignedState) (v w : ℤ) (u hp hm : List SmallSlot)
    (hden : a.frequency*((u.map SmallSlot.value).prod:ℤ)≠0)
    (hd : a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣
      reversalNumerator v w (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
        (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ))) :
    (signedPivot a v w u hp hm:ℝ)=
      (-(w:ℝ)*((hp.map SmallSlot.value).prod:ℝ)/
        ((a.frequency:ℝ)*((u.map SmallSlot.value).prod:ℝ)))*(a.giantPlus:ℝ)+
      ((v:ℝ)*((hm.map SmallSlot.value).prod:ℝ)/
        ((a.frequency:ℝ)*((u.map SmallSlot.value).prod:ℝ)))*(a.giantMinus:ℝ) := by
  have hs : (a.frequency:ℝ)≠0 := by exact_mod_cast (mul_ne_zero_iff.mp hden).1
  have hu : ((u.map SmallSlot.value).prod:ℝ)≠0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hden).2
  apply LinearReversal.pivot_linear hs hu
  have hh := congrArg (fun z : ℤ => (z:ℝ)) (signedPivot_reversal a v w u hp hm hd)
  simpa only [reversalNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using hh

def SignedHistory.ExactReversals : {l : ℕ} → SignedHistory l → Prop
  | _,.leaf _ => True
  | _,.node a p u hp hm left right =>
    reversalNumerator left.root.frequency right.root.frequency
      (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ))=
        a.frequency*((u.map SmallSlot.value).prod:ℤ)*p ∧
      left.ExactReversals ∧ right.ExactReversals

theorem signedDecode_exactReversals (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (hi : (signedDecode sources seed V l a c).PositiveIntegral) :
    (signedDecode sources seed V l a c).ExactReversals := by
  induction l generalizing a with
  | zero => trivial
  | succ l ih =>
    refine ⟨?_,ih _ c.2.2.2.1 hi.2.2.2.2.1,ih _ c.2.2.2.2 hi.2.2.2.2.2⟩
    have hd := hi.2.2.2.1
    simp only [signedDecode_root] at hd
    simpa only [signedDecode_root] using signedPivot_reversal a c.1.val c.2.1.val _ _ _ hd

theorem signedDecode_toHistory_of_positiveIntegral
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l)
    (hi : (signedDecode sources seed V l a c).PositiveIntegral) :
    (signedDecode sources seed V l a c).toHistory=decodeHistory sources seed V l a.toState c :=
  signedDecode_toHistory_of_nonnegative sources seed V l a c hi.nonnegative

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
