import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesPrecision
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSupportReductionArithmetic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSupportReduction

theorem natAbs_coprime_iff_of_modEq {a b d : ℤ} (h : a ≡ b [ZMOD d]) :
    Nat.Coprime a.natAbs d.natAbs ↔ Nat.Coprime b.natAbs d.natAbs := by
  change Int.gcd a d = 1 ↔ Int.gcd b d = 1
  rw [←Int.gcd_emod a d,←Int.gcd_emod b d]
  rw [show a % d=b % d from h]

theorem nat_coprime_iff_of_modEq {a b : ℤ} {d : ℕ} (h : a ≡ b [ZMOD (d:ℤ)]) :
    Nat.Coprime a.natAbs d ↔ Nat.Coprime b.natAbs d := by
  simpa only [Int.natAbs_natCast] using natAbs_coprime_iff_of_modEq h

theorem Congruent.frequencies_eq {N : ℤ} {l : ℕ} {h k : SignedHistory l}
    (hc : Congruent N h k) : frequencies h=frequencies k := by
  induction h with
  | leaf a =>
    cases k with
    | leaf b => exact congrArg (fun s => [s]) hc.1
  | node a p u hp hm left right il ir =>
    cases k with
    | node b q v kp km left' right' =>
      simp only [frequencies,hc.1.1,il hc.2.2.2.2.2.1,ir hc.2.2.2.2.2.2]

def Covers (N : ℤ) : {l : ℕ} → SignedHistory l → Prop
  | _,h@(.leaf a) => (∀v∈frequencies h,v ∣ N) ∧
      (∀q∈a.small,(q.value:ℤ) ∣ N) ∧ True
  | _,h@(.node a _ u _ _ left right) =>
      (∀v∈frequencies h,v ∣ N) ∧ (∀q∈a.small,(q.value:ℤ) ∣ N) ∧
      a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣ N ∧
      (∀q∈u,(q.value:ℤ)*(q.value:ℤ) ∣ N) ∧ Covers N left ∧ Covers N right

theorem rootArithmetic_iff_of_congruent {N : ℤ} {l : ℕ} (V : ℕ → ℕ)
    {h k : SignedHistory l} (hc : Congruent N h k) (hn : Covers N h) :
    RootArithmetic V h ↔ RootArithmetic V k := by
  have hfcover : ∀v∈frequencies h,v ∣ N := by cases h <;> exact hn.1
  have hs := hc.root
  have hf := hc.frequencies_eq
  simp only [RootArithmetic,←hs.1,←hs.2.1,←hf]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  exact and_congr
    (natAbs_coprime_iff_of_modEq (hs.2.2.1.of_dvd (hfcover v hv)))
    (natAbs_coprime_iff_of_modEq (hs.2.2.2.of_dvd (hfcover v hv)))

theorem localArithmetic_iff_of_congruent {N : ℤ} (outside : List ℕ)
    (hout : ∀q∈outside,(q:ℤ) ∣ N) (a b : SignedState) (p q : ℤ)
    (u hp hm : List SmallSlot) (v w : ℤ)
    (hc : StateCongruent N a b) (hpq : p ≡ q [ZMOD N])
    (hsq : ∀r∈u,(r.value:ℤ)*(r.value:ℤ) ∣ N) :
    LocalArithmetic outside a p u hp hm v w ↔ LocalArithmetic outside b q u hp hm v w := by
  have hnum : reversalNumerator v w (a.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (a.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) ≡
      reversalNumerator v w (b.giantPlus*((hp.map SmallSlot.value).prod:ℤ))
      (b.giantMinus*((hm.map SmallSlot.value).prod:ℤ)) [ZMOD N] :=
    ((hc.2.2.2.mul_right _).mul_left v).sub ((hc.2.2.1.mul_right _).mul_left w)
  unfold LocalArithmetic
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr
  · apply forall_congr'
    intro r
    apply forall_congr'
    intro hr
    exact not_congr ((hnum.of_dvd (hsq r hr)).dvd_iff)
  · apply and_congr_left
    intro _
    apply forall_congr'
    intro r
    apply forall_congr'
    intro hr
    exact nat_coprime_iff_of_modEq (hpq.of_dvd (hout r hr))

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
