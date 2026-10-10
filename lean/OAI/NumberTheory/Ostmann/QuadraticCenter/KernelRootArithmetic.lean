import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter

theorem complementary_divisor_dvd_sum {m t r : ℤ} (hm : m ≠ 0)
    (hroot : m ∣ t ^ 2 - r ^ 2) :
    m / ((t - r).gcd m : ℤ) ∣ t + r := by
  have hdpos : 0 < (t - r).gcd m := Int.gcd_pos_of_ne_zero_right _ hm
  have hcop : IsCoprime ((t - r) / ((t - r).gcd m : ℤ))
      (m / ((t - r).gcd m : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hdpos)
  have hprod : m ∣ (t - r) * (t + r) := by convert hroot using 1; ring
  have hd := Int.ediv_dvd_ediv (Int.gcd_dvd_right (t - r) m) hprod
  rw [Int.mul_ediv_assoc' _ (Int.gcd_dvd_left (t - r) m)] at hd
  exact hcop.symm.dvd_of_dvd_mul_left hd

theorem complementary_gcd_dvd_two {m : ℕ} (hm : 0 < m) {t r : ℤ}
    (hr : IsCoprime r (m : ℤ)) (hroot : (m : ℤ) ∣ t ^ 2 - r ^ 2) :
    Nat.gcd ((t - r).gcd (m : ℤ)) (m / ((t - r).gcd (m : ℤ))) ∣ 2 := by
  let d := (t - r).gcd (m : ℤ)
  let g := m / d
  have hdm : d ∣ m := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right (t - r) m)
  have hds : (d : ℤ) ∣ t - r := Int.gcd_dvd_left (t - r) m
  have hgs : (g : ℤ) ∣ t + r := by
    simpa only [g, d, Int.natCast_div] using
      complementary_divisor_dvd_sum (by exact_mod_cast hm.ne') hroot
  have hgd : (Nat.gcd d g : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.gcd_dvd_left d g
  have hgg : (Nat.gcd d g : ℤ) ∣ (g : ℤ) := by exact_mod_cast Nat.gcd_dvd_right d g
  have hgm : (Nat.gcd d g : ℤ) ∣ (m : ℤ) :=
    hgd.trans (Int.natCast_dvd_natCast.mpr hdm)
  have hgr : IsCoprime (Nat.gcd d g : ℤ) r :=
    hr.symm.of_isCoprime_of_dvd_left hgm
  have hg2r : (Nat.gcd d g : ℤ) ∣ 2 * r := by
    convert dvd_sub (hgg.trans hgs) (hgd.trans hds) using 1; ring
  exact Int.natCast_dvd_natCast.mp (hgr.dvd_of_dvd_mul_right hg2r)

theorem same_gcd_label_dvd_double_difference {m : ℕ} (hm : 0 < m)
    {t s r : ℤ} (hr : IsCoprime r (m : ℤ))
    (ht : (m : ℤ) ∣ t ^ 2 - r ^ 2)
    (hs : (m : ℤ) ∣ s ^ 2 - r ^ 2)
    (hlabel : (t - r).gcd (m : ℤ) = (s - r).gcd (m : ℤ)) :
    (m : ℤ) ∣ 2 * (t - s) := by
  let d := (t - r).gcd (m : ℤ)
  let g := m / d
  have hdm : d ∣ m := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right (t - r) m)
  have hdprod : d * g = m := Nat.mul_div_cancel' hdm
  have hdt : (d : ℤ) ∣ t - r := Int.gcd_dvd_left (t - r) m
  have hds : (d : ℤ) ∣ s - r := by
    simpa only [d, hlabel] using Int.gcd_dvd_left (s - r) m
  have hgt : (g : ℤ) ∣ t + r := by
    simpa only [g, d, Int.natCast_div] using
      complementary_divisor_dvd_sum (by exact_mod_cast hm.ne') ht
  have hgs : (g : ℤ) ∣ s + r := by
    simpa only [g, d, hlabel, Int.natCast_div] using
      complementary_divisor_dvd_sum (by exact_mod_cast hm.ne') hs
  have hdd : (d : ℤ) ∣ t - s := by convert dvd_sub hdt hds using 1; ring
  have hgd : (g : ℤ) ∣ t - s := by convert dvd_sub hgt hgs using 1; ring
  have hld : Nat.lcm d g ∣ (t - s).natAbs :=
    Nat.lcm_dvd (Int.natCast_dvd.mp hdd) (Int.natCast_dvd.mp hgd)
  have hg2 : Nat.gcd d g ∣ 2 := complementary_gcd_dvd_two hm hr ht
  have hmul : m ∣ 2 * (t - s).natAbs := by
    rw [← hdprod, ← Nat.gcd_mul_lcm]
    exact mul_dvd_mul hg2 hld
  apply Int.natCast_dvd.mpr
  simpa [Int.natAbs_mul] using hmul

end Ostmann.QuadraticCenter

end OAI
