import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeSupportedIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReduction

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSupportReduction
open Construction HistorySignedDecode

def frequencies : {l : ℕ}→SignedHistory l→List ℤ
  | _,.leaf a => [a.frequency]
  | _,.node a _ _ _ _ left right => a.frequency::(frequencies left++frequencies right)

@[simp] theorem toHistory_root {l : ℕ} (h : SignedHistory l) : h.toHistory.root=h.root.toState := by
  cases h <;> rfl
@[simp] theorem toHistory_frequencies {l : ℕ} (h : SignedHistory l) :
    h.toHistory.frequencies=frequencies h := by
  induction h with
  | leaf a => rfl
  | node a p u hp hm left right il ir =>
    simp only [SignedHistory.toHistory,History.frequencies,frequencies,il,ir,SignedState.toState]

def RootData (V : ℕ→ℕ) {l : ℕ} (h : SignedHistory l) : Prop :=
  h.root.toState.Positive ∧ (∀q∈h.root.small,q.value.Prime) ∧
    (∀q∈h.root.small,∀j,q.role=.compensation j→l<j) ∧
    h.root.frequency≠0 ∧ h.root.frequency.natAbs≤V l ∧
    ∀v∈frequencies h,Nat.Coprime h.root.giantPlus.toNat v.natAbs ∧
      Nat.Coprime h.root.giantMinus.toNat v.natAbs

def LocalTests (outside : List ℕ) (a : SignedState) (p : ℤ)
    (u hp hm : List SmallSlot) (v w : ℤ) : Prop :=
  (u.map SmallSlot.value).Nodup ∧ (∀b∈u,Nat.Prime b.value) ∧
    (∀b∈u,¬(b.value:ℤ)*b.value ∣ reversalNumerator v w
      (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ))) ∧
    (∀q∈outside,Nat.Coprime p.toNat q) ∧ (∀b∈u,∀q∈outside,Nat.Coprime b.value q)

def NodeRelations (l : ℕ) (a : SignedState) (p : ℤ) (u hp hm : List SmallSlot)
    (b c : SignedState) : Prop :=
  0<p ∧ (∀q∈u,q.role=.compensation l) ∧ a.small.Perm (hp++hm) ∧
    b.giantPlus=p ∧ c.giantPlus=p ∧ b.giantMinus=a.giantPlus ∧ c.giantMinus=a.giantMinus ∧
    b.small.Perm (u++hp) ∧ c.small.Perm (u++hm) ∧
    reversalNumerator b.frequency c.frequency
      (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ))=
        a.frequency*((u.map SmallSlot.value).prod:ℤ)*p

theorem rootData_iff_projection (V : ℕ→ℕ) {l : ℕ} (h : SignedHistory l) :
    RootData V h↔HistorySupportReduction.RootData V h.toHistory := by
  simp only [RootData,HistorySupportReduction.RootData,toHistory_root,State.PrimeSmall,
    State.TemplateAt,History.GiantUnits,toHistory_frequencies,SignedState.toState]

theorem localTests_iff_projection (outside : List ℕ) (a : SignedState) (p : ℤ)
    (u hp hm : List SmallSlot) (v w : ℤ) (ha : a.Nonnegative) :
    LocalTests outside a p u hp hm v w↔
      HistorySupportReduction.LocalTests outside a.toState p.toNat u hp hm v w := by
  simp only [LocalTests,HistorySupportReduction.LocalTests,SignedState.toState,Nat.cast_mul,
    Int.toNat_of_nonneg ha.1,Int.toNat_of_nonneg ha.2]

lemma toNat_eq_iff {a b : ℤ} (ha : 0≤a) (hb : 0≤b) : a.toNat=b.toNat↔a=b := by omega

theorem nodeRelations_iff_projection (l : ℕ) (a : SignedState) (p : ℤ)
    (u hp hm : List SmallSlot) (b c : SignedState)
    (ha : a.Nonnegative) (hb : b.Nonnegative) (hc : c.Nonnegative) (hp0 : 0≤p) :
    NodeRelations l a p u hp hm b c↔
      History.nodeRelations l a.toState p.toNat u hp hm b.toState c.toState := by
  have hpos : 0<p.toNat↔0<p := by omega
  simp only [NodeRelations,History.nodeRelations,SignedState.toState,hpos,
    toNat_eq_iff hb.1 hp0,toNat_eq_iff hc.1 hp0,toNat_eq_iff hb.2 ha.1,toNat_eq_iff hc.2 ha.2,
    Nat.cast_mul,Int.toNat_of_nonneg ha.1,Int.toNat_of_nonneg ha.2,Int.toNat_of_nonneg hp0]

end Ostmann.Arithmetic.HistorySignedSupportReduction

end

end OAI
