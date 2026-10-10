import OAI.Combinatorics.EditApproximation.Binary.BinaryArithmeticWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Most-significant comparison performed directly on little-endian Boolean
words, allowing leading zero bits. -/

namespace EditApproximation





theorem bitOrdering_matches (high : Ordering) (a b : Bool) (x y : ℕ)
    (h : orderingMatches high x y) :
    orderingMatches (bitOrdering high a b) (a.toNat + 2 * x) (b.toNat + 2 * y) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, by cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩
  · cases a <;> cases b <;> simp [bitOrdering, orderingMatches]
  · exact Or.inr (Or.inr ⟨rfl, by
      cases a <;> cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega⟩)





theorem bitCompareWithWork_matches (left right : List Bool) :
    orderingMatches (bitCompareWithWork left right).1 (bitWordValue left) (bitWordValue right) := by
  induction left generalizing right with
  | nil =>
    simp only [bitCompareWithWork]
    induction right with
    | nil => simp [bitCompareNilLeftWithWork, orderingMatches, bitWordValue]
    | cons b bs ih =>
      simpa only [bitCompareNilLeftWithWork, bitWordValue, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
        Nat.zero_add] using bitOrdering_matches (bitCompareNilLeftWithWork bs).1 false b 0 (bitWordValue bs) ih
  | cons a as ih =>
    cases right with
    | nil =>
      simpa only [bitCompareWithWork, bitWordValue, Bool.toNat_false, Nat.add_zero, Nat.mul_zero,
        Nat.zero_add] using bitOrdering_matches (bitCompareWithWork as []).1 a false (bitWordValue as) 0 (ih [])
    | cons b bs =>
      simpa only [bitCompareWithWork, bitWordValue] using
        bitOrdering_matches (bitCompareWithWork as bs).1 a b (bitWordValue as) (bitWordValue bs) (ih bs)

theorem bitCompareWithWork_lt (left right : List Bool) :
    (bitCompareWithWork left right).1 = .lt ↔ bitWordValue left < bitWordValue right := by
  have h := bitCompareWithWork_matches left right
  rcases h with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;> rw [h] <;> simp_all
  all_goals omega

theorem bitCompareWithWork_eq (left right : List Bool) :
    (bitCompareWithWork left right).1 = .eq ↔ bitWordValue left = bitWordValue right := by
  have h := bitCompareWithWork_matches left right
  rcases h with ⟨h, hv⟩ | ⟨h, hv⟩ | ⟨h, hv⟩ <;> rw [h] <;> simp_all
  all_goals omega

theorem bitCompareWithWork_cost (left right : List Bool) :
    (bitCompareWithWork left right).2 ≤ 4 * (left.length + right.length) + 1 := by
  induction left generalizing right with
  | nil =>
    simp only [bitCompareWithWork]
    induction right with
    | nil => simp [bitCompareNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitCompareNilLeftWithWork, List.length_cons, List.length_nil] at *
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih []
      simp only [bitCompareWithWork, List.length_cons, List.length_nil] at *
      omega
    | cons b bs =>
      have h := ih bs
      simp only [bitCompareWithWork, List.length_cons] at *
      omega



theorem binaryNaturalCompareWithWork_lt (a b : ℕ) :
    (binaryNaturalCompareWithWork a b).1 = .lt ↔ a < b := by
  simpa only [binaryNaturalCompareWithWork, bitWordValue_bits] using bitCompareWithWork_lt a.bits b.bits

theorem binaryNaturalCompareWithWork_eq (a b : ℕ) :
    (binaryNaturalCompareWithWork a b).1 = .eq ↔ a = b := by
  simpa only [binaryNaturalCompareWithWork, bitWordValue_bits] using bitCompareWithWork_eq a.bits b.bits

theorem binaryNaturalCompareWithWork_cost (a b : ℕ) :
    (binaryNaturalCompareWithWork a b).2 ≤ 4 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalCompareWithWork, Nat.size_eq_bits_len] using bitCompareWithWork_cost a.bits b.bits

end EditApproximation

end OAI
