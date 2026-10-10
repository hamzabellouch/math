import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticEncodingSize

namespace OAI

section

namespace KS.W01

def sumBudget (xs : List ℚ) : ℕ := (xs.map ratLength).sum + xs.length

@[simp] theorem sumBudget_nil : sumBudget [] = 0 := rfl

@[simp] theorem sumBudget_cons (q : ℚ) (xs : List ℚ) :
    sumBudget (q :: xs) = ratLength q + sumBudget xs + 1 := by
  simp only [sumBudget, List.map_cons, List.sum_cons, List.length_cons]
  omega

theorem sum_parts_le_two_pow (xs : List ℚ) :
    xs.sum.num.natAbs ≤ 2 ^ sumBudget xs ∧ xs.sum.den ≤ 2 ^ sumBudget xs := by
  induction xs with
  | nil => simp [sumBudget]
  | cons q xs ih =>
    obtain ⟨hqn, hqd⟩ := rational_parts_le_two_pow_length q
    obtain ⟨hn, hd⟩ := KS.W30.add_parts_le_two_pow q xs.sum
      (ratLength q) (sumBudget xs) hqn hqd ih.1 ih.2
    constructor
    · simpa only [List.sum_cons, sumBudget_cons] using hn
    · simp only [List.sum_cons, sumBudget_cons]
      exact hd.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem ratLength_sum_le (xs : List ℚ) :
    ratLength xs.sum ≤ 4 * ((xs.map ratLength).sum + xs.length) + 7 := by
  obtain ⟨hn, hd⟩ := sum_parts_le_two_pow xs
  have h := ratLength_le_of_parts xs.sum (sumBudget xs) (sumBudget xs) hn hd
  unfold sumBudget at h
  omega

theorem prod_parts_le_two_pow (xs : List ℚ) :
    xs.prod.num.natAbs ≤ 2 ^ (xs.map ratLength).sum ∧
      xs.prod.den ≤ 2 ^ (xs.map ratLength).sum := by
  induction xs with
  | nil => simp
  | cons q xs ih =>
    obtain ⟨hqn, hqd⟩ := rational_parts_le_two_pow_length q
    obtain ⟨hn, hd⟩ := KS.W30.mul_parts_le_two_pow q xs.prod
      (ratLength q) (xs.map ratLength).sum hqn hqd ih.1 ih.2
    simpa only [List.prod_cons, List.map_cons, List.sum_cons] using And.intro hn hd

theorem ratLength_prod_le (xs : List ℚ) :
    ratLength xs.prod ≤ 4 * (xs.map ratLength).sum + 7 := by
  obtain ⟨hn, hd⟩ := prod_parts_le_two_pow xs
  have h := ratLength_le_of_parts xs.prod _ _ hn hd
  omega

end KS.W01

end

end OAI
