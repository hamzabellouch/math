import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTResidue
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistory

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorGiantIndependence
open Construction HistorySignedSpectatorCRT

theorem residueSpectator_decode_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (N : ℕ)
    (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (hf : a.frequency=b.frequency) (hs : a.small=b.small) (Xp Xm : ZMod N) :
    residueSpectator g outside N (decodeHistory sources seed V l a c) Xp Xm =
      residueSpectator g outside N (decodeHistory sources seed V l b c) Xp Xm := by
  induction l generalizing a b Xp Xm with
  | zero => simp only [decodeHistory,residueSpectator,residueLeaf,hf,hs]
  | succ l ih =>
    simp only [decodeHistory,residueSpectator,decodeHistory_root,residuePivot,hf,hs]
    apply congrArg₂ (fun x y : ℂ => x*conj y)
    · apply ih <;> rfl
    · apply ih <;> rfl

theorem residuePairSpectator_decode_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (N : ℕ)
    (l : ℕ) (a b a' b' : State) (c e : HistoryChoices sources seed V l)
    (hf : a.frequency=b.frequency) (hs : a.small=b.small)
    (hf' : a'.frequency=b'.frequency) (hs' : a'.small=b'.small) (z : ZMod N×ZMod N) :
    residuePairSpectator g outside N (decodeHistory sources seed V l a c)
      (decodeHistory sources seed V l a' e) z =
    residuePairSpectator g outside N (decodeHistory sources seed V l b c)
      (decodeHistory sources seed V l b' e) z := by
  unfold residuePairSpectator
  rw [residueSpectator_decode_eq sources seed V g outside N l a b c hf hs,
    residueSpectator_decode_eq sources seed V g outside N l a' b' e hf' hs']

end Ostmann.Arithmetic.HistoryBulkSpectatorGiantIndependence

end

end OAI
