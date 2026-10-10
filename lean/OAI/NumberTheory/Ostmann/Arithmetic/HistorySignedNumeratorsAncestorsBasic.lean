import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsLinear

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction HistoryOccurrenceVariables HistorySignedDecode

def AncestorIntegralGuard : {l : ℕ} → (h : History l) → ℤ → ℤ → InternalKey h → Prop
  | _, .leaf _, _, _ => fun i => nomatch i
  | _, .node a _ u hp hm left right, Xp, Xm =>
    let b : SignedState := ⟨a.frequency, Xp, Xm, a.small⟩
    let p := signedPivot b left.root.frequency right.root.frequency u hp hm
    let den := a.frequency * ((u.map SmallSlot.value).prod : ℤ)
    let num := reversalNumerator left.root.frequency right.root.frequency
      (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ))
    Sum.elim (fun _ => True) (Sum.elim
      (fun i => den ≠ 0 ∧ den ∣ num ∧ AncestorIntegralGuard left p Xp i)
      (fun i => den ≠ 0 ∧ den ∣ num ∧ AncestorIntegralGuard right p Xm i))

@[simp] theorem ancestorIntegralGuard_current {l : ℕ} (a : State) (p : ℕ)
    (u hp hm : List SmallSlot) (left right : History l) (Xp Xm : ℤ) (i : Fin u.length) :
    AncestorIntegralGuard (.node a p u hp hm left right) Xp Xm (Sum.inl i) := trivial

@[simp] theorem ancestorIntegralGuard_left {l : ℕ} (a : State) (p : ℕ)
    (u hp hm : List SmallSlot) (left right : History l) (Xp Xm : ℤ) (i : InternalKey left) :
    AncestorIntegralGuard (.node a p u hp hm left right) Xp Xm (Sum.inr (Sum.inl i)) ↔
      a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0 ∧
      a.frequency * ((u.map SmallSlot.value).prod : ℤ) ∣
        reversalNumerator left.root.frequency right.root.frequency
          (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ)) ∧
      AncestorIntegralGuard left
        (signedPivot ⟨a.frequency, Xp, Xm, a.small⟩ left.root.frequency right.root.frequency u hp hm)
        Xp i := Iff.rfl

@[simp] theorem ancestorIntegralGuard_right {l : ℕ} (a : State) (p : ℕ)
    (u hp hm : List SmallSlot) (left right : History l) (Xp Xm : ℤ) (i : InternalKey right) :
    AncestorIntegralGuard (.node a p u hp hm left right) Xp Xm (Sum.inr (Sum.inr i)) ↔
      a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0 ∧
      a.frequency * ((u.map SmallSlot.value).prod : ℤ) ∣
        reversalNumerator left.root.frequency right.root.frequency
          (Xp * ((hp.map SmallSlot.value).prod : ℤ)) (Xm * ((hm.map SmallSlot.value).prod : ℤ)) ∧
      AncestorIntegralGuard right
        (signedPivot ⟨a.frequency, Xp, Xm, a.small⟩ left.root.frequency right.root.frequency u hp hm)
        Xm i := Iff.rfl

theorem ancestorIntegralGuard_of_integralGuard {l : ℕ} (h : History l) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (i : InternalKey h) :
    AncestorIntegralGuard h Xp Xm i := by
  induction h generalizing Xp Xm with
  | leaf a => exact isEmptyElim i
  | node a p u hp hm left right ihl ihr =>
    simp only [rebuild, SignedHistory.IntegralGuard, rebuild_root] at hi
    rcases i with i | i
    · trivial
    · rcases i with i | i
      · exact ⟨hi.1, hi.2.1, ihl _ _ hi.2.2.1 i⟩
      · exact ⟨hi.1, hi.2.1, ihr _ _ hi.2.2.2 i⟩

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI
