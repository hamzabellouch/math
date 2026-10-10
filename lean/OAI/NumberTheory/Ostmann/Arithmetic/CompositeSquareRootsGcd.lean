import Mathlib

namespace OAI

namespace Ostmann.Arithmetic

theorem int_dvd_cross_of_square_gcd_eq (n a b : ℤ)
    (hb : n ∣ (b - 1) * (b + 1))
    (hg : Int.gcd n (a - 1) = Int.gcd n (b - 1)) :
    n ∣ (a - 1) * (b + 1) := by
  have hd : n ∣ (Int.gcd n (b - 1) : ℤ) * (b + 1) := by
    rw [Int.gcd_eq_gcd_ab]
    convert dvd_add (dvd_mul_right n (Int.gcdA n (b - 1) * (b + 1)))
      (dvd_mul_of_dvd_left hb (Int.gcdB n (b - 1))) using 1
    ring
  rw [← hg] at hd
  obtain ⟨k, hk⟩ := Int.gcd_dvd_right n (a - 1)
  rw [hk]
  convert dvd_mul_of_dvd_left hd k using 1
  ring

theorem int_dvd_two_sub_of_square_gcd_eq (n a b : ℤ)
    (ha : n ∣ (a - 1) * (a + 1)) (hb : n ∣ (b - 1) * (b + 1))
    (hg : Int.gcd n (a - 1) = Int.gcd n (b - 1)) :
    n ∣ 2 * (a - b) := by
  have hab := int_dvd_cross_of_square_gcd_eq n a b hb hg
  have hba := int_dvd_cross_of_square_gcd_eq n b a ha hg.symm
  convert dvd_sub hab hba using 1
  ring

theorem nat_eq_of_two_sub_dvd_of_halfIndex_eq {n a b : ℕ} (_hn : 0 < n)
    (_ha : a < n) (_hb : b < n)
    (hd : (n : ℤ) ∣ 2 * ((a : ℤ) - b))
    (hq : 2 * a / n = 2 * b / n) : a = b := by
  have hm : (2 * a : ℕ) % n = (2 * b : ℕ) % n := by
    have hmod : (2 * (b : ℤ)) ≡ 2 * (a : ℤ) [ZMOD (n : ℤ)] := by
      apply Int.modEq_iff_dvd.mpr
      convert hd using 1
      ring
    have hmod' : (2 * b : ℕ) ≡ (2 * a : ℕ) [MOD n] := by
      exact_mod_cast hmod
    exact hmod'.symm
  have heq := Nat.mod_add_div (2 * a) n
  have heq' := Nat.mod_add_div (2 * b) n
  rw [hq, hm] at heq
  omega

end Ostmann.Arithmetic

end OAI
