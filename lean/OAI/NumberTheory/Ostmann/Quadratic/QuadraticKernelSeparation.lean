import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace OAI

/-! # Disjoint prime supports of the two endpoint kernel populations -/

namespace Ostmann

/-- A prime divisor of a kernel cannot divide the reduced denominator. -/
theorem kernel_prime_not_dvd_denominator (m : ℕ) (h x u t : ℤ)
    (hred : h.natAbs.Coprime m) (heq : u * t ^ 2 = (m : ℤ) * x - h)
    {p : ℕ} (hp : p.Prime) (hpu : p ∣ u.natAbs) : ¬p ∣ m := by
  intro hpm
  have hpu' : (p : ℤ) ∣ u := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpu)
  have hpm' : (p : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hpm
  have hph : (p : ℤ) ∣ h := by
    have hh := dvd_sub (dvd_mul_of_dvd_left hpm' x) (dvd_mul_of_dvd_left hpu' (t ^ 2))
    convert hh using 1
    linear_combination heq
  have hph' : p ∣ h.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hph)
  have hg := Nat.dvd_gcd hph' hpm
  rw [hred] at hg
  exact hp.not_dvd_one hg

/-- The sumset primality condition forces opposite-side kernels to have
disjoint prime factors. This is valid for signed kernels and endpoints. -/
theorem quadratic_kernels_coprime (m : ℕ) (h x y u v s t : ℤ)
    (hu0 : u ≠ 0)
    (hred : h.natAbs.Coprime m)
    (hx : u * s ^ 2 = (m : ℤ) * x - h)
    (hy : v * t ^ 2 = (m : ℤ) * y - h)
    (hprime : (x - y).natAbs.Prime)
    (hsmall : u.natAbs < (x - y).natAbs) :
    u.natAbs.Coprime v.natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp hpu hpv
  have hpm := kernel_prime_not_dvd_denominator m h x u s hred hx hp hpu
  have hu : (p : ℤ) ∣ u := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpu)
  have hv : (p : ℤ) ∣ v := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpv)
  have hdiff : (p : ℤ) ∣ (m : ℤ) * (x - y) := by
    have hh := dvd_sub (dvd_mul_of_dvd_left hu (s ^ 2)) (dvd_mul_of_dvd_left hv (t ^ 2))
    convert hh using 1
    linear_combination -hx + hy
  have hn : p ∣ m * (x - y).natAbs := by
    have habs := Int.natAbs_dvd_natAbs.mpr hdiff
    simpa only [Int.natAbs_natCast, Int.natAbs_mul] using habs
  have hpn : p ∣ (x - y).natAbs := (hp.dvd_mul.mp hn).resolve_left hpm
  have heq : p = (x - y).natAbs :=
    (hprime.eq_one_or_self_of_dvd p hpn).resolve_left hp.ne_one
  have hup : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  exact (not_le_of_gt hsmall) (heq ▸ Nat.le_of_dvd hup hpu)

end Ostmann

end OAI
