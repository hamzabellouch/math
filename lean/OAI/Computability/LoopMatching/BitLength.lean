import OAI.Computability.LoopMatching.BitAdd

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching.BitAdd

lemma value_lt_two_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;>
      simp only [value, Bool.toNat_false, Bool.toNat_true, List.length_cons,
        pow_succ] <;> omega

lemma length_bits_value_le (xs : List Bool) : (value xs).bits.length ≤ xs.length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (value_lt_two_pow_length xs)

lemma length_bits_value_add (xs ys : List Bool) :
    (value xs + value ys).bits.length ≤ max xs.length ys.length + 1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hx : value xs < 2 ^ max xs.length ys.length :=
    (value_lt_two_pow_length xs).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hy : value ys < 2 ^ max xs.length ys.length :=
    (value_lt_two_pow_length ys).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  rw [pow_succ]
  omega

lemma length_bits_value_add_le (xs ys : List Bool) (a b : ℕ)
    (hx : xs.length ≤ a) (hy : ys.length ≤ b) :
    (value xs + value ys).bits.length ≤ max a b + 1 := by
  exact (length_bits_value_add xs ys).trans (by omega)

end LoopMatching.BitAdd

end OAI
