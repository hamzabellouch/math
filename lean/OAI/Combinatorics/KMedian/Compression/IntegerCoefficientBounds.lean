import Mathlib

namespace OAI

namespace MetricKMedian.Compression

theorem gram_coefficient_bit_bound (r n L : ℕ) (hn : n ≤ r) :
    (n.factorial:ℤ)*((r:ℤ)*((2:ℤ)^L)^2)^n ≤ (2:ℤ)^(2*r*(r+L)) := by
  have hnr : n ≤ 2^r := hn.trans Nat.lt_two_pow_self.le
  have hf : n.factorial ≤ 2^(r*r) := by
    calc
      _ ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^r)^n := Nat.pow_le_pow_left hnr n
      _ = 2^(r*n) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left r hn)
  have hfZ : (n.factorial:ℤ) ≤ 2^(r*r) := by exact_mod_cast hf
  have hrZ : (r:ℤ) ≤ 2^r := by exact_mod_cast (Nat.lt_two_pow_self (n:=r)).le
  have hb : (r:ℤ)*((2:ℤ)^L)^2 ≤ 2^(r+2*L) := by
    calc
      _ ≤ 2^r*((2:ℤ)^L)^2 := mul_le_mul_of_nonneg_right hrZ (sq_nonneg _)
      _ = _ := by rw [pow_add,Nat.mul_comm 2 L,pow_mul]
  have hbn : ((r:ℤ)*((2:ℤ)^L)^2)^n ≤ 2^((r+2*L)*r) := by
    calc
      _ ≤ ((2:ℤ)^(r+2*L))^n := pow_le_pow_left₀ (by positivity) hb n
      _ = 2^((r+2*L)*n) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hn)
  calc
    _ ≤ 2^(r*r)*(2:ℤ)^((r+2*L)*r) :=
      mul_le_mul hfZ hbn (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end MetricKMedian.Compression

end OAI
