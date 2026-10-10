import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorPeriodic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSpectatorCRT
open Construction HistorySignedDecode HistorySignedResidues

theorem quotient_modEq_integral {a b d N : ℤ} (ha : d∣a) (hb : d∣b)
    (hc : Nat.Coprime d.natAbs N.natAbs) (h : a≡b [ZMOD N]) :
    a/d≡b/d [ZMOD N] := by
  apply Int.modEq_iff_dvd.mpr
  apply Int.dvd_of_dvd_mul_right_of_gcd_one _ hc.symm
  rw [mul_sub,Int.mul_ediv_cancel' hb,Int.mul_ediv_cancel' ha]
  exact Int.modEq_iff_dvd.mp h

theorem signedPivot_modEq_integral {N : ℤ} (a : State) (v w : ℤ)
    (u hp hm : List SmallSlot) (Xp Xm Yp Ym : ℤ)
    (hc : Nat.Coprime (a.frequency*((u.map SmallSlot.value).prod:ℤ)).natAbs N.natAbs)
    (hx : a.frequency*((u.map SmallSlot.value).prod:ℤ)∣
      reversalNumerator v w (Xp*((hp.map SmallSlot.value).prod:ℤ))
        (Xm*((hm.map SmallSlot.value).prod:ℤ)))
    (hy : a.frequency*((u.map SmallSlot.value).prod:ℤ)∣
      reversalNumerator v w (Yp*((hp.map SmallSlot.value).prod:ℤ))
        (Ym*((hm.map SmallSlot.value).prod:ℤ)))
    (hplus : Xp≡Yp [ZMOD N]) (hminus : Xm≡Ym [ZMOD N]) :
    signedPivot ⟨a.frequency,Xp,Xm,a.small⟩ v w u hp hm≡
      signedPivot ⟨a.frequency,Yp,Ym,a.small⟩ v w u hp hm [ZMOD N] := by
  apply quotient_modEq_integral hx hy hc
  exact ((hminus.mul_right _).mul_left v).sub ((hplus.mul_right _).mul_left w)

theorem rebuild_congruent_integral {l : ℕ} (h : History l) (R N Xp Xm Yp Ym : ℤ)
    (hd : DivisorData R h) (hc : Nat.Coprime R.natAbs N.natAbs)
    (hx : (rebuild h Xp Xm).IntegralGuard) (hy : (rebuild h Yp Ym).IntegralGuard)
    (hplus : Xp≡Yp [ZMOD N]) (hminus : Xm≡Ym [ZMOD N]) :
    Congruent N (rebuild h Xp Xm) (rebuild h Yp Ym) := by
  induction h generalizing Xp Xm Yp Ym with
  | leaf a => exact ⟨rfl,rfl,hplus,hminus⟩
  | node a p u hp hm left right il ir =>
    simp only [rebuild,SignedHistory.IntegralGuard,rebuild_root] at hx hy
    have hcop : Nat.Coprime (a.frequency*((u.map SmallSlot.value).prod:ℤ)).natAbs N.natAbs :=
      hc.of_dvd_left (Int.natAbs_dvd_natAbs.mpr hd.2.1)
    have hpivot := signedPivot_modEq_integral a left.root.frequency right.root.frequency
      u hp hm Xp Xm Yp Ym hcop hx.2.1 hy.2.1 hplus hminus
    refine ⟨⟨rfl,rfl,hplus,hminus⟩,hpivot,rfl,rfl,rfl,?_,?_⟩
    · exact il _ _ _ _ hd.2.2.1 hx.2.2.1 hy.2.2.1 hpivot hplus
    · exact ir _ _ _ _ hd.2.2.2 hx.2.2.2 hy.2.2.2 hpivot hminus

end Ostmann.Arithmetic.HistorySignedSpectatorCRT

end

end OAI
