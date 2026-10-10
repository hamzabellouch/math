import OAI.NumberTheory.Ostmann.Construction.CanonicalHistory

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction

structure SignedState where
  frequency : ℤ
  giantPlus : ℤ
  giantMinus : ℤ
  small : List SmallSlot
  deriving DecidableEq

def SignedState.ofState (a : State) : SignedState :=
  ⟨a.frequency,a.giantPlus,a.giantMinus,a.small⟩

def SignedState.toState (a : SignedState) : State :=
  ⟨a.frequency,a.giantPlus.toNat,a.giantMinus.toNat,a.small⟩

def SignedState.Nonnegative (a : SignedState) : Prop :=
  0≤a.giantPlus ∧ 0≤a.giantMinus

@[simp] theorem SignedState.toState_ofState (a : State) : (SignedState.ofState a).toState=a := by
  cases a
  rfl

inductive SignedHistory : ℕ → Type
  | leaf (state : SignedState) : SignedHistory 0
  | node {l : ℕ} (state : SignedState) (pivot : ℤ)
      (compensation plusSmall minusSmall : List SmallSlot)
      (left right : SignedHistory l) : SignedHistory (l+1)

def SignedHistory.root : {l : ℕ} → SignedHistory l → SignedState
  | _,.leaf a => a
  | _,.node a _ _ _ _ _ _ => a

def SignedHistory.toHistory : {l : ℕ} → SignedHistory l → History l
  | _,.leaf a => .leaf a.toState
  | _,.node a p u hp hm left right =>
    .node a.toState p.toNat u hp hm left.toHistory right.toHistory

def SignedHistory.Nonnegative : {l : ℕ} → SignedHistory l → Prop
  | _,.leaf a => a.Nonnegative
  | _,.node a p _ _ _ left right =>
    a.Nonnegative ∧ 0≤p ∧ left.Nonnegative ∧ right.Nonnegative

def signedPivot (a : SignedState) (v w : ℤ) (u hp hm : List SmallSlot) : ℤ :=
  reversalNumerator v w (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
    (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) /
      (a.frequency*((u.map SmallSlot.value).prod:ℤ))

def signedDecode (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) :
    (l : ℕ) → SignedState → HistoryChoices sources seed V l → SignedHistory l
  | 0,a,_ => .leaf a
  | l+1,a,c =>
    let T := Template.current seed l
    let u := assignedSlots sources (Template.extracted (l+1) T) c.2.2.1
    let n := (Template.remainder (l+1) T).length
    let hp := a.small.take n
    let hm := a.small.drop n
    let p := signedPivot a c.1.val c.2.1.val u hp hm
    let al : SignedState := ⟨c.1.val,p,a.giantPlus,Template.reinsert (l+1) T u hp⟩
    let ar : SignedState := ⟨c.2.1.val,p,a.giantMinus,Template.reinsert (l+1) T u hm⟩
    .node a p u hp hm
      (signedDecode sources seed V l al c.2.2.2.1)
      (signedDecode sources seed V l ar c.2.2.2.2)

@[simp] theorem signedDecode_root (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (a : SignedState) (c : HistoryChoices sources seed V l) :
    (signedDecode sources seed V l a c).root=a := by
  cases l <;> rfl

theorem signedPivot_toNat (a : SignedState) (ha : a.Nonnegative) (v w : ℤ)
    (u hp hm : List SmallSlot) :
    (signedPivot a v w u hp hm).toNat=decodedPivot a.toState v w u hp hm := by
  simp only [signedPivot,decodedPivot,SignedState.toState,Nat.cast_mul,
    Int.toNat_of_nonneg ha.1,Int.toNat_of_nonneg ha.2]

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
