import OAI.Combinatorics.EditApproximation.Queries.QueryInputCodes

namespace OAI

/-! Quadratic work bounds for actual duplicate removal and encoded sorting.
The bound counts comparisons and list allocation, including duplicates. -/

namespace EditApproximation

theorem queryEraseLoopWithWork_length {α : Type*} (equal : α → α → Bool × ℕ)
    (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).1.length ≤ xs.length + seen.length := by
  induction xs generalizing seen with
  | nil => simp only [queryEraseLoopWithWork, List.length_reverse, List.length_nil, Nat.zero_add, le_refl]
  | cons a xs ih =>
    change (queryEraseLoopWithWork equal xs
      (if (memberByWithWork equal a seen).1 then seen else a :: seen)).1.length ≤ _
    split_ifs
    · exact (ih seen).trans (by simp only [List.length_cons]; omega)
    · exact (ih (a :: seen)).trans (by simp only [List.length_cons]; omega)

theorem queryEraseWithWork_length {α : Type*} (equal : α → α → Bool × ℕ) (xs : List α) :
    (queryEraseWithWork equal xs).1.length ≤ xs.length := by
  simpa only [queryEraseWithWork, List.length_nil, Nat.add_zero] using
    queryEraseLoopWithWork_length equal xs []

theorem queryOrderedInputsWithWork_cost {α : Type*}
    (encode : α → ℕ) (equal le : α → α → Bool × ℕ)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b))
    (C D : ℕ) (hequal : ∀ a b, (equal a b).2 ≤ C) (horder : ∀ a b, (le a b).2 ≤ D)
    (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).2 ≤
      (xs.length + 1) ^ 2 * (C + D + 8) := by
  have he := queryEraseWithWork_cost equal C hequal xs
  have hs := querySortWithWork_cost (fun a b => encode a ≤ encode b) le hle D horder
    (queryEraseWithWork equal xs).1
  have hl := queryEraseWithWork_length equal xs
  have hp : ((queryEraseWithWork equal xs).1.length + 1) ^ 2 ≤ (xs.length + 1) ^ 2 := by
    gcongr
  have hb := hs.trans (Nat.mul_le_mul_right (D + 3) hp)
  change (queryEraseWithWork equal xs).2 + _ + 1 ≤ _
  nlinarith only [he, hb, Nat.zero_le C, Nat.zero_le D, Nat.zero_le xs.length]

theorem queryEncodedLEWithWork_cost {α : Type*} (code : α → ℕ × ℕ)
    (a b : α) (C B : ℕ) (ha : (code a).2 ≤ C) (hb : (code b).2 ≤ C)
    (hva : Nat.size (code a).1 ≤ B) (hvb : Nat.size (code b).1 ≤ B) :
    (queryEncodedLEWithWork code a b).2 ≤ 2 * C + 10 * B + 5 := by
  have hc := wordLEWithWork_cost (code a).1.bits (code b).1.bits
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hc
  change _ + _ + _ + _ + _ + 3 ≤ _
  omega

end EditApproximation

end OAI
