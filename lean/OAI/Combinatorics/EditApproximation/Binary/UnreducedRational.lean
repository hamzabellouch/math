import OAI.Combinatorics.EditApproximation.Numerics.RationalIntermediateBits
import OAI.Combinatorics.EditApproximation.Binary.BinaryArithmeticWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Exact fractions with positive, unreduced denominators. These operations
perform no greatest-common-divisor computation. The representation lemmas
apply to the intermediate fractions, not merely their reduced Rat values. -/

namespace EditApproximation



namespace UnreducedRational

theorem eq_of_num_den {a b : UnreducedRational} (hnum : a.num = b.num) (hden : a.den = b.den) : a = b := by
  cases a
  cases b
  cases hnum
  cases hden
  rfl



def ofRat (a : ℚ) : UnreducedRational := ⟨a.num, a.den, a.den_pos⟩



def add (a b : UnreducedRational) : UnreducedRational :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def neg (a : UnreducedRational) : UnreducedRational := ⟨-a.num, a.den, a.den_pos⟩







def le (a b : UnreducedRational) : Bool := decide (a.num * b.den ≤ b.num * a.den)



def storageBits (a : UnreducedRational) : ℕ := Nat.size a.num.natAbs + Nat.size a.den + 1

@[simp] theorem value_ofRat (a : ℚ) : (ofRat a).value = a := by
  exact a.num_div_den

@[simp] theorem value_zero : zero.value = 0 := by simp [zero, value]

@[simp] theorem value_add (a b : UnreducedRational) : (a.add b).value = a.value + b.value := by
  unfold add value
  push_cast
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  field_simp [ha, hb]

@[simp] theorem value_neg (a : UnreducedRational) : a.neg.value = -a.value := by
  simp [neg, value, neg_div]

@[simp] theorem value_mul (a b : UnreducedRational) : (a.mul b).value = a.value * b.value := by
  simp [mul, value, mul_div_mul_comm]

@[simp] theorem value_inv (a : UnreducedRational) : a.inv.value = a.value⁻¹ := by
  by_cases h : a.num = 0
  · simp [inv, h, value, zero]
  · have hn : (a.num.natAbs : ℚ) ≠ 0 := by exact_mod_cast (Int.natAbs_pos.mpr h).ne'
    have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
    have hsign : ((a.num.sign : ℤ) : ℚ) * a.num = (a.num.natAbs : ℚ) := by
      simpa only [Int.cast_mul, Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ℚ)) (Int.sign_mul_self_eq_natAbs a.num)
    simp only [inv, h, ↓reduceDIte, value]
    push_cast
    apply eq_inv_of_mul_eq_one_left
    field_simp [hn, hd]
    exact hsign

@[simp] theorem value_div (a b : UnreducedRational) : (a.div b).value = a.value / b.value := by
  simp [div, div_eq_mul_inv]

@[simp] theorem le_eq_true (a b : UnreducedRational) : a.le b = true ↔ a.value ≤ b.value := by
  simp only [le, decide_eq_true_eq, value]
  rw [div_le_div_iff₀ (by exact_mod_cast a.den_pos : (0 : ℚ) < a.den)
    (by exact_mod_cast b.den_pos : (0 : ℚ) < b.den)]
  exact_mod_cast (Iff.rfl : a.num * (b.den : ℤ) ≤ b.num * (a.den : ℤ) ↔ _)

@[simp] theorem lt_eq_true (a b : UnreducedRational) : a.lt b = true ↔ a.value < b.value := by
  simp only [lt, decide_eq_true_eq, value]
  rw [div_lt_div_iff₀ (by exact_mod_cast a.den_pos : (0 : ℚ) < a.den)
    (by exact_mod_cast b.den_pos : (0 : ℚ) < b.den)]
  exact_mod_cast (Iff.rfl : a.num * (b.den : ℤ) < b.num * (a.den : ℤ) ↔ _)

theorem add_den_bits (a b : UnreducedRational) :
    Nat.size (a.add b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

theorem mul_den_bits (a b : UnreducedRational) :
    Nat.size (a.mul b).den ≤ Nat.size a.den + Nat.size b.den :=
  natural_product_bit_length _ _

theorem num_abs_le (a : UnreducedRational) (V : ℕ) (hvalue : |a.value| ≤ V) :
    a.num.natAbs ≤ V * a.den := by
  have hscaled := mul_le_mul_of_nonneg_right hvalue
    (show (0 : ℚ) ≤ a.den by exact_mod_cast a.den_pos.le)
  have hnum : |a.value| * (a.den : ℚ) = (a.num.natAbs : ℚ) := by
    unfold value
    rw [abs_div, abs_of_pos (by exact_mod_cast a.den_pos : (0 : ℚ) < a.den)]
    rw [div_mul_cancel₀ _ (by exact_mod_cast a.den_pos.ne' : (a.den : ℚ) ≠ 0)]
    simp [Int.cast_abs]
  rw [hnum] at hscaled
  exact_mod_cast hscaled

theorem storageBits_le (a : UnreducedRational) (V D : ℕ)
    (hvalue : |a.value| ≤ V) (hden : Nat.size a.den ≤ D) :
    a.storageBits ≤ Nat.size V + 2 * D + 1 := by
  have hnum := (Nat.size_le_size (a.num_abs_le V hvalue)).trans
    (natural_product_bit_length V a.den)
  unfold storageBits
  omega

end UnreducedRational

end EditApproximation

end OAI
