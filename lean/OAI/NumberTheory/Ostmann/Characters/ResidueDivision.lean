import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.ResidueDivision
attribute [local instance] Classical.propDecidable

theorem quotient_eq_of_intCast_eq (N M:ℕ) (s a b:ℤ) (hs:s≠0)
    (hNM:s.natAbs*M∣N) (ha:s∣a) (hb:s∣b)
    (hab:(a:ZMod N)=(b:ZMod N)) : ((a/s:ℤ):ZMod M)=((b/s:ℤ):ZMod M) := by
  have hd : s*(M:ℤ)∣(N:ℤ) := Int.dvd_natCast.mpr (by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using hNM)
  have hmod := (ZMod.intCast_eq_intCast_iff a b N).mp hab
  have hcancel : s*(a/s)≡s*(b/s) [ZMOD s*(M:ℤ)] := by
    simpa only [Int.mul_ediv_cancel' ha,Int.mul_ediv_cancel' hb] using hmod.of_dvd hd
  exact (ZMod.intCast_eq_intCast_iff _ _ M).mpr (Int.ModEq.mul_left_cancel' hs hcancel)

def divideResidue (N M:ℕ) (s:ℤ) (z:ZMod N) : ZMod M :=
  if h:∃a:ℤ,(a:ZMod N)=z ∧ s∣a then ((Classical.choose h/s:ℤ):ZMod M) else 0

theorem divideResidue_intCast (N M:ℕ) (s a:ℤ) (hs:s≠0)
    (hNM:s.natAbs*M∣N) (ha:s∣a) :
    divideResidue N M s (a:ZMod N)=((a/s:ℤ):ZMod M) := by
  have hex : ∃b:ℤ,(b:ZMod N)=(a:ZMod N) ∧ s∣b := ⟨a,rfl,ha⟩
  rw [divideResidue,dite_eq_left hex]
  exact quotient_eq_of_intCast_eq N M s _ a hs hNM (Classical.choose_spec hex).2 ha
    (Classical.choose_spec hex).1

theorem divideResidue_reversal (N M:ℕ) (s v w HL HR P:ℤ) (hs:s≠0)
    (hNM:s.natAbs*M∣N) (h:s*P=v*HR-w*HL) :
    divideResidue N M s ((v:ZMod N)*HR-w*HL)=(P:ZMod M) := by
  have ha : s∣v*HR-w*HL := ⟨P,h.symm⟩
  have he : (v*HR-w*HL)/s=P :=
    mul_left_cancel₀ hs ((Int.mul_ediv_cancel' ha).trans h.symm)
  simpa only [Int.cast_sub,Int.cast_mul,he] using
    divideResidue_intCast N M s (v*HR-w*HL) hs hNM ha

def unitDivideResidue (N M:ℕ) (s:ℤ) (u:(ZMod M)ˣ) (z:ZMod N) : ZMod M :=
  divideResidue N M s z * ↑(u⁻¹)

theorem unitDivideResidue_reversal (N M:ℕ) (s u v w HL HR P:ℤ)
    (U:(ZMod M)ˣ) (hU:(u:ZMod M)=U) (hs:s≠0)
    (hNM:s.natAbs*M∣N) (h:s*u*P=v*HR-w*HL) :
    unitDivideResidue N M s U ((v:ZMod N)*HR-w*HL)=(P:ZMod M) := by
  unfold unitDivideResidue
  rw [divideResidue_reversal N M s v w HL HR (u*P) hs hNM (by simpa only [mul_assoc] using h)]
  simp only [Int.cast_mul,hU]
  rw [mul_right_comm,← Units.val_mul, mul_inv_cancel,Units.val_one,one_mul]

theorem frequency_power_divides (R:ℕ) (s:ℤ) (hs:s.natAbs∣R) (k:ℕ) :
    s.natAbs*R^k∣R^(k+1) := by
  rw [pow_succ']
  exact mul_dvd_mul hs (dvd_refl (R^k))

end Ostmann.Characters.ResidueDivision

end

end OAI
