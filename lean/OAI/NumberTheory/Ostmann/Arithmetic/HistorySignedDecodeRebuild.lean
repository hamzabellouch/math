import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeIntegral

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction

def SignedHistory.IntegralGuard : {l : ℕ} → SignedHistory l → Prop
  | _,.leaf _ => True
  | _,.node a _ u hp hm left right =>
    a.frequency*((u.map SmallSlot.value).prod:ℤ)≠0 ∧
      a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣
        reversalNumerator left.root.frequency right.root.frequency
          (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
          (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) ∧
      left.IntegralGuard ∧ right.IntegralGuard

def SignedHistory.PivotsPositive : {l : ℕ} → SignedHistory l → Prop
  | _,.leaf _ => True
  | _,.node _ p _ _ _ left right => 0<p ∧ left.PivotsPositive ∧ right.PivotsPositive

theorem SignedHistory.PositiveIntegral.integralGuard {l : ℕ} {h : SignedHistory l}
    (hi : h.PositiveIntegral) : h.IntegralGuard := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
    exact ⟨hi.2.2.1,hi.2.2.2.1,il hi.2.2.2.2.1,ir hi.2.2.2.2.2⟩

def rebuild : {l : ℕ} → History l → ℤ → ℤ → SignedHistory l
  | _,.leaf a,Xp,Xm => .leaf ⟨a.frequency,Xp,Xm,a.small⟩
  | _,.node a _ u hp hm left right,Xp,Xm =>
    let b : SignedState := ⟨a.frequency,Xp,Xm,a.small⟩
    let p := signedPivot b left.root.frequency right.root.frequency u hp hm
    .node b p u hp hm (rebuild left p Xp) (rebuild right p Xm)

@[simp] theorem rebuild_root {l : ℕ} (h : History l) (Xp Xm : ℤ) :
    (rebuild h Xp Xm).root=⟨h.root.frequency,Xp,Xm,h.root.small⟩ := by
  cases h <;> rfl

theorem rebuild_decodeHistory (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (Xp Xm : ℤ) :
    rebuild (decodeHistory sources seed V l a c) Xp Xm=
      signedDecode sources seed V l ⟨a.frequency,Xp,Xm,a.small⟩ c := by
  induction l generalizing a Xp Xm with
  | zero => rfl
  | succ l ih =>
    simp only [decodeHistory,rebuild,decodeHistory_root,signedDecode,ih]

theorem rebuild_nonnegative_of_pivotsPositive {l : ℕ} (h : History l) (Xp Xm : ℤ)
    (hp : 0≤Xp) (hm : 0≤Xm) (hi : (rebuild h Xp Xm).PivotsPositive) :
    (rebuild h Xp Xm).Nonnegative := by
  induction h generalizing Xp Xm with
  | leaf a => exact ⟨hp,hm⟩
  | node a p u hplus hminus left right il ir =>
    exact ⟨⟨hp,hm⟩,hi.1.le,il _ _ hi.1.le hp hi.2.1,ir _ _ hi.1.le hm hi.2.2⟩

theorem rebuild_positiveIntegral {l : ℕ} (h : History l) (Xp Xm : ℤ)
    (hp : 0<Xp) (hm : 0<Xm) (hi : (rebuild h Xp Xm).IntegralGuard)
    (hpos : (rebuild h Xp Xm).PivotsPositive) :
    (rebuild h Xp Xm).PositiveIntegral := by
  induction h generalizing Xp Xm with
  | leaf a => exact ⟨hp,hm⟩
  | node a p u hplus hminus left right il ir =>
    exact ⟨⟨hp,hm⟩,hpos.1,hi.1,hi.2.1,
      il _ _ hpos.1 hp hi.2.2.1 hpos.2.1,ir _ _ hpos.1 hm hi.2.2.2 hpos.2.2⟩

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
