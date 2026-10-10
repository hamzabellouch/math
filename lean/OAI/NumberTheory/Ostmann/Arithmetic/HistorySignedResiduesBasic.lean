import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeRebuild

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode

theorem quotient_modEq {a b d N : ℤ} (hd : d ≠ 0)
    (h : a ≡ b [ZMOD d*N]) : a/d ≡ b/d [ZMOD N] := by
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp h
  have hb : b = a + (N*t)*d := by linarith [ht]
  rw [hb,Int.add_mul_ediv_right _ _ hd]
  apply Int.modEq_iff_dvd.mpr
  exact ⟨t,by ring⟩

def StateCongruent (N : ℤ) (a b : SignedState) : Prop :=
  a.frequency=b.frequency ∧ a.small=b.small ∧
    a.giantPlus ≡ b.giantPlus [ZMOD N] ∧ a.giantMinus ≡ b.giantMinus [ZMOD N]

def Congruent (N : ℤ) : {l : ℕ} → SignedHistory l → SignedHistory l → Prop
  | _,.leaf a,.leaf b => StateCongruent N a b
  | _,.node a p u hp hm left right,.node b q v kp km left' right' =>
      StateCongruent N a b ∧ p ≡ q [ZMOD N] ∧
      u=v ∧ hp=kp ∧ hm=km ∧ Congruent N left left' ∧ Congruent N right right'

theorem Congruent.root {N : ℤ} {l : ℕ} {h k : SignedHistory l}
    (hc : Congruent N h k) : StateCongruent N h.root k.root := by
  cases h <;> cases k
  · exact hc
  · exact hc.1

theorem Congruent.of_dvd {N M : ℤ} {l : ℕ} {h k : SignedHistory l}
    (hc : Congruent N h k) (hd : M ∣ N) : Congruent M h k := by
  induction h with
  | leaf a =>
    cases k with
    | leaf b => exact ⟨hc.1,hc.2.1,hc.2.2.1.of_dvd hd,hc.2.2.2.of_dvd hd⟩
  | node a p u hp hm left right il ir =>
    cases k with
    | node b q v kp km left' right' =>
      exact ⟨⟨hc.1.1,hc.1.2.1,hc.1.2.2.1.of_dvd hd,hc.1.2.2.2.of_dvd hd⟩,
        hc.2.1.of_dvd hd,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,
        il hc.2.2.2.2.2.1,ir hc.2.2.2.2.2.2⟩

def DivisorData (R : ℤ) : {l : ℕ} → History l → Prop
  | _,.leaf _ => True
  | _,.node a _ u _ _ left right =>
      a.frequency*((u.map SmallSlot.value).prod:ℤ)≠0 ∧
      a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣ R ∧
      DivisorData R left ∧ DivisorData R right

theorem precision_dvd (R N : ℤ) (l : ℕ) : R^l*N ∣ R^(l+1)*N := by
  refine ⟨R,?_⟩
  rw [pow_succ]
  ring

theorem divisor_precision_dvd {R d N : ℤ} (hd : d ∣ R) (l : ℕ) :
    d*(R^l*N) ∣ R^(l+1)*N := by
  obtain ⟨t,ht⟩ := hd
  refine ⟨t,?_⟩
  rw [pow_succ,ht]
  ring

theorem signedPivot_modEq {R N : ℤ} {l : ℕ} (a : State) (v w : ℤ)
    (u hp hm : List SmallSlot) (Xp Xm Yp Ym : ℤ)
    (hd : a.frequency*((u.map SmallSlot.value).prod:ℤ)≠0)
    (hdiv : a.frequency*((u.map SmallSlot.value).prod:ℤ) ∣ R)
    (hplus : Xp ≡ Yp [ZMOD R^(l+1)*N]) (hminus : Xm ≡ Ym [ZMOD R^(l+1)*N]) :
    signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ v w u hp hm ≡
      signedPivot ⟨a.frequency,Yp,Ym,a.small⟩ v w u hp hm [ZMOD R^l*N] := by
  apply quotient_modEq hd
  exact (((hminus.mul_right _).mul_left v).sub ((hplus.mul_right _).mul_left w)).of_dvd
    (divisor_precision_dvd hdiv l)

theorem rebuild_congruent {l : ℕ} (h : History l) (R N Xp Xm Yp Ym : ℤ)
    (hd : DivisorData R h)
    (hplus : Xp ≡ Yp [ZMOD R^l*N]) (hminus : Xm ≡ Ym [ZMOD R^l*N]) :
    Congruent N (rebuild h Xp Xm) (rebuild h Yp Ym) := by
  induction h generalizing Xp Xm Yp Ym with
  | leaf a =>
    exact ⟨rfl,rfl,by simpa using hplus,by simpa using hminus⟩
  | @node l a p u hp hm left right il ir =>
    have hpivot := signedPivot_modEq a left.root.frequency right.root.frequency u hp hm
      Xp Xm Yp Ym hd.1 hd.2.1 hplus hminus
    have hdown := precision_dvd R N l
    have hN : N ∣ R^l*N := dvd_mul_left N (R^l)
    refine ⟨⟨rfl,rfl,(hplus.of_dvd hdown).of_dvd hN,
      (hminus.of_dvd hdown).of_dvd hN⟩,hpivot.of_dvd hN,rfl,rfl,rfl,?_,?_⟩
    · exact il _ _ _ _ hd.2.2.1 hpivot (hplus.of_dvd hdown)
    · exact ir _ _ _ _ hd.2.2.2 hpivot (hminus.of_dvd hdown)

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
