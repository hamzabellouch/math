import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyMultiplicity
import OAI.NumberTheory.Ostmann.Characters.SquareCongruence

namespace OAI

noncomputable section
namespace Ostmann.Characters

theorem dvd_of_unit_congruence (n d : ℕ) (hdn : d∣n) (v w : ℤ)
    (u u' : (ZMod n)ˣ) (hdv : (d:ℤ)∣v)
    (h : (v:ZMod n)*u=(w:ZMod n)*u') : (d:ℤ)∣w := by
  let φ := ZMod.castHom hdn (ZMod d)
  have hh := congrArg φ h
  have hv : (v:ZMod d)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd v d).mpr hdv
  have hw : (w:ZMod d)*(Units.map φ.toMonoidHom u' : (ZMod d)ˣ)=0 := by
    change (w:ZMod d)*φ (u':ZMod n)=0
    simpa only [map_mul, map_intCast, hv, zero_mul] using hh.symm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd w d).mp
    ((Units.map φ.toMonoidHom u').mul_left_eq_zero.mp hw)

theorem gcd_eq_of_unit_congruence (n : ℕ) (v w : ℤ) (u u' : (ZMod n)ˣ)
    (h : (v:ZMod n)*u=(w:ZMod n)*u') : v.natAbs.gcd n=w.natAbs.gcd n := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
    have hdv : ((v.natAbs.gcd n : ℕ):ℤ)∣v :=
      Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    exact Int.natCast_dvd.mp
      (dvd_of_unit_congruence n _ (Nat.gcd_dvd_right _ _) v w u u' hdv h)
  · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
    have hdw : ((w.natAbs.gcd n : ℕ):ℤ)∣w :=
      Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
    exact Int.natCast_dvd.mp
      (dvd_of_unit_congruence n _ (Nat.gcd_dvd_right _ _) w v u' u hdw h.symm)

theorem triple_gcd_eq (v w : ℤ) (n : ℕ)
    (h : v.natAbs.gcd n=w.natAbs.gcd n) :
    (v.natAbs.gcd w.natAbs).gcd n=v.natAbs.gcd n := by
  rw [Nat.gcd_assoc, ← h, ← Nat.gcd_assoc, Nat.gcd_self]

theorem cancel_common_divisor (n g : ℕ) (hg : 0<g) (hgn : g∣n)
    (v w U V : ℤ) (hgv : (g:ℤ)∣v) (hgw : (g:ℤ)∣w)
    (h : (n:ℤ)∣v*U-w*V) :
    ((n/g:ℕ):ℤ)∣(v/(g:ℤ))*U-(w/(g:ℤ))*V := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k,?_⟩
  have hgz : (g:ℤ)≠0 := by exact_mod_cast hg.ne'
  apply mul_left_cancel₀ hgz
  have hn : (g:ℤ)*((n/g:ℕ):ℤ)=(n:ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hgn
  have hv : (g:ℤ)*(v/(g:ℤ))=v := Int.mul_ediv_cancel' hgv
  have hw : (g:ℤ)*(w/(g:ℤ))=w := Int.mul_ediv_cancel' hgw
  calc
    (g:ℤ)*((v/(g:ℤ))*U-(w/(g:ℤ))*V) = v*U-w*V := by
      rw [mul_sub, ← mul_assoc, hv, ← mul_assoc, hw]
    _ = (n:ℤ)*k := hk
    _ = (g:ℤ)*(((n/g:ℕ):ℤ)*k) := by rw [← mul_assoc, hn]

theorem reduced_frequency_isUnit (n : ℕ) [NeZero n] (v : ℤ) :
    IsUnit ((v/(v.natAbs.gcd n:ℕ):ℤ) : ZMod (n/(v.natAbs.gcd n))) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr
  apply isCoprime_comm.mp
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  have hg : 0<Int.gcd v (n:ℤ) := by
    change 0<v.natAbs.gcd n
    exact Nat.gcd_pos_of_pos_right _ (NeZero.pos n)
  have hh := Int.gcd_ediv_gcd_ediv_gcd hg
  simpa only [Int.gcd_def, Int.natAbs_natCast, Int.natCast_div] using hh

end Ostmann.Characters

end

end OAI
