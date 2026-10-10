import OAI.Combinatorics.EditApproximation.Binary.BinaryFixedDenominator
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Construction of a prescribed power denominator uses literal Boolean
multiplication and trimming. The subsequent cache compression therefore has
no uncharged conversion from a natural number to its binary representation. -/

namespace EditApproximation



theorem bitPowerWithWork_value (base : List Bool) (n : ℕ) :
    bitWordValue (bitPowerWithWork base n).1 = bitWordValue base ^ n := by
  induction n with
  | zero => simp [bitPowerWithWork, bitWordValue]
  | succ n ih =>
    simp only [bitPowerWithWork, trimBitWordWithWork_value, bitMulWithWork_value, ih, pow_succ]

theorem bitPowerWithWork_length (base : List Bool) (n : ℕ) :
    (bitPowerWithWork base n).1.length = Nat.size (bitWordValue base ^ n) := by
  cases n with
  | zero => simp [bitPowerWithWork]
  | succ n =>
    simp only [bitPowerWithWork, trimBitWordWithWork_length, bitMulWithWork_value,
      bitPowerWithWork_value, pow_succ]

theorem bitPowerWithWork_length_le (base : List Bool) (n B : ℕ) (hB : base.length ≤ B) :
    (bitPowerWithWork base n).1.length ≤ n * B + 1 := by
  rw [bitPowerWithWork_length]
  exact (natural_power_bit_length _ _).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left n
      ((Nat.size_le.mpr (bitWordValue_lt_pow_length base)).trans hB)) 1)

def bitPowerBitBudget (n B : ℕ) : ℕ :=
  1 + n * (200 * ((n + 1) * (B + 1) + 1) ^ 2)

theorem bitPowerWithWork_cost (base : List Bool) (n B : ℕ) (hB : base.length ≤ B) :
    (bitPowerWithWork base n).2 ≤ bitPowerBitBudget n B := by
  let W := (n + 1) * (B + 1)
  have hbase : base.length ≤ W := by
    have := Nat.le_mul_of_pos_left (B + 1) (by omega : 0 < n + 1)
    dsimp only [W]
    omega
  have hwidth (j : ℕ) (hj : j ≤ n) : (bitPowerWithWork base j).1.length ≤ W := by
    have hb := bitPowerWithWork_length_le base j B hB
    have hm := Nat.mul_le_mul_right B hj
    dsimp only [W]
    nlinarith only [hb, hm, Nat.zero_le n, Nat.zero_le B]
  have hcost (j : ℕ) (hj : j ≤ n) :
      (bitPowerWithWork base j).2 ≤ 1 + j * (200 * (W + 1) ^ 2) := by
    induction j with
    | zero => simp [bitPowerWithWork]
    | succ j ih =>
      have hj' : j ≤ n := by omega
      have hi := ih hj'
      have hw := hwidth j hj'
      let previous := bitPowerWithWork base j
      let product := bitMulWithWork previous.1 base
      change previous.1.length ≤ W at hw
      have hp := bitMulWithWork_cost previous.1 base
      have hpl := bitMulWithWork_length previous.1 base
      have ht := trimBitWordWithWork_cost product.1
      change product.2 ≤ _ at hp
      have hstep : product.2 + (trimBitWordWithWork product.1).2 + 2 ≤ 200 * (W + 1) ^ 2 := by
        have hmul := Nat.mul_le_mul (show previous.1.length + 1 ≤ W + 1 by omega)
          (show previous.1.length + base.length + 1 ≤ 2 * W + 1 by omega)
        change product.1.length ≤ 2 * previous.1.length + base.length + 1 at hpl
        nlinarith only [hp, hpl, ht, hmul, hw, hbase, Nat.zero_le W]
      change (bitPowerWithWork base j).2 + product.2 + (trimBitWordWithWork product.1).2 + 2 ≤ _
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact hcost n le_rfl



theorem refinementBaseWithWork_value (ell : List Bool) :
    bitWordValue (refinementBaseWithWork ell).1 = bitWordValue ell ^ 10 + 1 := by
  simp only [refinementBaseWithWork, trimBitWordWithWork_value, bitAddWithWork_value,
    bitPowerWithWork_value, bitWordValue, Bool.toNat_true, Bool.toNat_false]

theorem refinementBaseWithWork_length (ell : List Bool) :
    (refinementBaseWithWork ell).1.length = Nat.size (bitWordValue ell ^ 10 + 1) := by
  simp only [refinementBaseWithWork, trimBitWordWithWork_length, bitAddWithWork_value,
    bitPowerWithWork_value, bitWordValue, Bool.toNat_true, Bool.toNat_false]

theorem refinementBaseWithWork_length_le (ell : List Bool) (B : ℕ) (hB : ell.length ≤ B) :
    (refinementBaseWithWork ell).1.length ≤ 10 * B + 3 := by
  rw [refinementBaseWithWork_length]
  have hp := natural_power_bit_length (bitWordValue ell) 10
  have hs := natural_sum_bit_length (bitWordValue ell ^ 10) 1
  have hb := (Nat.size_le.mpr (bitWordValue_lt_pow_length ell)).trans hB
  simp only [Nat.size_one] at hs
  omega

theorem refinementBaseWithWork_cost (ell : List Bool) (B : ℕ) (hB : ell.length ≤ B) :
    (refinementBaseWithWork ell).2 ≤ bitPowerBitBudget 10 B + 200 * (B + 1) := by
  have hp := bitPowerWithWork_cost ell 10 B hB
  have hpl := bitPowerWithWork_length_le ell 10 B hB
  have ha := bitAddWithWork_cost (bitPowerWithWork ell 10).1 [true] false
  have hal := bitAddWithWork_length (bitPowerWithWork ell 10).1 [true] false
  have ht := trimBitWordWithWork_cost (bitAddWithWork (bitPowerWithWork ell 10).1 [true] false).1
  simp only [List.length_cons, List.length_nil] at ha hal
  have hmax : max (bitPowerWithWork ell 10).1.length 1 ≤ 10 * B + 1 := max_le hpl (by omega)
  change (bitPowerWithWork ell 10).2 +
    (bitAddWithWork (bitPowerWithWork ell 10).1 [true] false).2 +
    (trimBitWordWithWork (bitAddWithWork (bitPowerWithWork ell 10).1 [true] false).1).2 + 2 ≤ _
  omega

namespace BinaryFraction



theorem powerDenominatorWithWork_value (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n : ℕ) (hden : a.value.den ∣ bitWordValue base ^ n) :
    (powerDenominatorWithWork a base hbase n).1.value = a.value := by
  apply fixedDenominatorWithWork_value
  simpa only [bitPowerWithWork_value] using hden

theorem powerDenominatorWithWork_width (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n V B : ℕ) (hB : base.length ≤ B)
    (hden : a.value.den ∣ bitWordValue base ^ n) (hv : |a.value| ≤ V) :
    (powerDenominatorWithWork a base hbase n).1.width ≤ Nat.size V + 2 * (n * B + 1) + 1 := by
  apply fixedDenominatorWithWork_width a (bitPowerWithWork base n).1 _ _ V (n * B + 1)
  · exact hv
  · exact bitPowerWithWork_length_le base n B hB
  · simpa only [bitPowerWithWork_value] using hden

def powerDenominatorBitBudget (n A B : ℕ) : ℕ :=
  bitPowerBitBudget n B + 5000 * (A + (n * B + 1) + 2) ^ 2 + 1

theorem powerDenominatorWithWork_cost (a : BinaryFraction) (base : List Bool)
    (hbase : 0 < bitWordValue base) (n A B : ℕ) (ha : a.width ≤ A) (hB : base.length ≤ B) :
    (powerDenominatorWithWork a base hbase n).2 ≤ powerDenominatorBitBudget n A B := by
  have hp := bitPowerWithWork_cost base n B hB
  have hf := fixedDenominatorWithWork_cost a (bitPowerWithWork base n).1
    (by rw [bitPowerWithWork_value]; exact Nat.pow_pos hbase) A (n * B + 1)
    ha (bitPowerWithWork_length_le base n B hB)
  change (bitPowerWithWork base n).2 + (fixedDenominatorWithWork a (bitPowerWithWork base n).1 _).2 + 1 ≤ _
  unfold powerDenominatorBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
