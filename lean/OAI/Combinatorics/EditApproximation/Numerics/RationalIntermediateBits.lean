import OAI.Combinatorics.EditApproximation.Numerics.NumericalWork

namespace OAI

/-! Bounds on the reduced integer representations produced by the rational
operations in the materialized numerical routines. -/

namespace EditApproximation

theorem rational_add_numerator_le (a b : ℚ) :
    (a + b).num.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den := by
  have heq := congrArg Int.natAbs (Rat.add_num_den' a b)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at heq
  have hadd := Int.natAbs_add_le (a.num * (b.den : ℤ)) (b.num * (a.den : ℤ))
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hadd
  have hden := Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos) (Rat.add_den_dvd a b)
  have hmul := Nat.mul_le_mul hadd hden
  have hpos := Nat.mul_pos a.den_pos b.den_pos
  nlinarith only [heq, hmul, hpos]

theorem rational_mul_numerator_le (a b : ℚ) :
    (a * b).num.natAbs ≤ a.num.natAbs * b.num.natAbs := by
  have heq := congrArg Int.natAbs (Rat.mul_num_den' a b)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at heq
  have hden := Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos) (Rat.mul_den_dvd a b)
  have hmul := Nat.mul_le_mul_left (a.num.natAbs * b.num.natAbs) hden
  have hpos := Nat.mul_pos a.den_pos b.den_pos
  nlinarith only [heq, hmul, hpos]

theorem rationalEncodingBits_add (a b : ℚ) :
    rationalEncodingBits (a + b) ≤ 2 * rationalEncodingBits a + 2 * rationalEncodingBits b + 2 := by
  have hnum := (Nat.size_le_size (rational_add_numerator_le a b)).trans
    (natural_sum_bit_length (a.num.natAbs * b.den) (b.num.natAbs * a.den))
  have hnum1 := natural_product_bit_length a.num.natAbs b.den
  have hnum2 := natural_product_bit_length b.num.natAbs a.den
  have hden := (Nat.size_le_size (Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos)
    (Rat.add_den_dvd a b))).trans (natural_product_bit_length a.den b.den)
  unfold rationalEncodingBits
  omega

theorem rationalEncodingBits_mul (a b : ℚ) :
    rationalEncodingBits (a * b) ≤ rationalEncodingBits a + rationalEncodingBits b + 1 := by
  have hnum := (Nat.size_le_size (rational_mul_numerator_le a b)).trans
    (natural_product_bit_length a.num.natAbs b.num.natAbs)
  have hden := (Nat.size_le_size (Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos)
    (Rat.mul_den_dvd a b))).trans (natural_product_bit_length a.den b.den)
  unfold rationalEncodingBits
  omega

theorem rationalEncodingBits_neg (a : ℚ) : rationalEncodingBits (-a) = rationalEncodingBits a := by
  simp [rationalEncodingBits]

theorem rationalEncodingBits_sub (a b : ℚ) :
    rationalEncodingBits (a - b) ≤ 2 * rationalEncodingBits a + 2 * rationalEncodingBits b + 2 := by
  simpa only [sub_eq_add_neg, rationalEncodingBits_neg] using rationalEncodingBits_add a (-b)

theorem rationalEncodingBits_inv (a : ℚ) :
    rationalEncodingBits a⁻¹ ≤ rationalEncodingBits a + 2 := by
  by_cases ha : a.num = 0
  · have hzero : a = 0 := Rat.zero_of_num_zero ha
    subst a
    norm_num [rationalEncodingBits]
  · simp only [rationalEncodingBits, Rat.num_inv, Rat.den_inv, ha, ↓reduceIte,
      Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_sign_of_ne_zero ha, Nat.one_mul]
    omega

theorem rationalEncodingBits_div (a b : ℚ) :
    rationalEncodingBits (a / b) ≤ rationalEncodingBits a + rationalEncodingBits b + 3 := by
  have hmul := rationalEncodingBits_mul a b⁻¹
  have hinv := rationalEncodingBits_inv b
  rw [div_eq_mul_inv]
  omega

theorem rationalEncodingBits_natCast (n : ℕ) :
    rationalEncodingBits (n : ℚ) = Nat.size n + 2 := by
  simp [rationalEncodingBits]

theorem rationalEncodingBits_pow (a : ℚ) (n : ℕ) :
    rationalEncodingBits (a ^ n) ≤ n * (rationalEncodingBits a + 1) + 3 := by
  induction n with
  | zero => norm_num [rationalEncodingBits]
  | succ n ih =>
    rw [pow_succ]
    have hmul := rationalEncodingBits_mul (a ^ n) a
    nlinarith only [ih, hmul]

end EditApproximation

end OAI
