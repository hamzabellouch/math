import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Finite support estimates for mask differences.
The label type is retained even when the products s_i collide. -/
namespace Dixmier

open Finset
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]

noncomputable def rowOnes (a : G → I → Bool) (x : G) : Finset I :=
  univ.filter fun i => a x i = true

noncomputable def columnZeros (a : G → I → Bool) (s : I → G) (y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i = false

noncomputable def rowDifference (a : G → I → Bool) (g x : G) : Finset I :=
  univ.filter fun i => a x i ≠ a (g⁻¹ * x) i

noncomputable def columnDifference (a : G → I → Bool) (s : I → G)
    (g y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i ≠ a (g⁻¹ * (y * (s i)⁻¹)) i

private theorem bool_ne_true_union (b c : Bool) (h : b ≠ c) :
    b = true ∨ c = true := by cases b <;> cases c <;> simp_all

private theorem bool_ne_false_union (b c : Bool) (h : b ≠ c) :
    b = false ∨ c = false := by cases b <;> cases c <;> simp_all

/-- A row difference is supported on the union of the two one-sets. -/
theorem rowDifference_subset (a : G → I → Bool) (g x : G) :
    rowDifference a g x ⊆ rowOnes a x ∪ rowOnes a (g⁻¹ * x) := by
  intro i hi
  simp only [rowDifference, rowOnes, mem_filter, mem_univ, true_and, mem_union] at *
  exact bool_ne_true_union _ _ hi

/-- Column support uses zero-sets at y and g⁻¹y. -/
theorem columnDifference_subset (a : G → I → Bool) (s : I → G) (g y : G) :
    columnDifference a s g y ⊆ columnZeros a s y ∪ columnZeros a s (g⁻¹ * y) := by
  intro i hi
  simp only [columnDifference, columnZeros, mem_filter, mem_univ, true_and,
    mem_union, mul_assoc] at *
  exact bool_ne_false_union _ _ hi

/-- The row support bound p=min(2r,n), without distinctness of group products. -/
theorem rowDifference_card_le (a : G → I → Bool) (r : ℕ)
    (hr : ∀ x, (rowOnes a x).card ≤ r) (g x : G) :
    (rowDifference a g x).card ≤ min (2 * r) (Fintype.card I) := by
  apply le_min
  · calc
      _ ≤ (rowOnes a x ∪ rowOnes a (g⁻¹ * x)).card := card_le_card (rowDifference_subset a g x)
      _ ≤ (rowOnes a x).card + (rowOnes a (g⁻¹ * x)).card := card_union_le _ _
      _ ≤ r + r := Nat.add_le_add (hr x) (hr (g⁻¹ * x))
      _ = 2 * r := (two_mul r).symm
  · exact card_le_univ _

/-- The column support bound p=min(2r,n). -/
theorem columnDifference_card_le (a : G → I → Bool) (s : I → G) (r : ℕ)
    (hc : ∀ y, (columnZeros a s y).card ≤ r) (g y : G) :
    (columnDifference a s g y).card ≤ min (2 * r) (Fintype.card I) := by
  apply le_min
  · calc
      _ ≤ (columnZeros a s y ∪ columnZeros a s (g⁻¹ * y)).card :=
        card_le_card (columnDifference_subset a s g y)
      _ ≤ (columnZeros a s y).card + (columnZeros a s (g⁻¹ * y)).card := card_union_le _ _
      _ ≤ r + r := Nat.add_le_add (hc y) (hc (g⁻¹ * y))
      _ = 2 * r := (two_mul r).symm
  · exact card_le_univ _

def boolComplex (b : Bool) : ℂ := if b then 1 else 0

/-- The scalar difference mask has absolute value at most one. -/
theorem difference_mask_norm (b c : Bool) : ‖boolComplex b - boolComplex c‖ ≤ 1 := by
  cases b <;> cases c <;> simp [boolComplex]

/-- Nonzero complex mask coefficients correspond exactly to unequal bits. -/
theorem difference_mask_ne_zero (b c : Bool) :
    boolComplex b - boolComplex c ≠ 0 ↔ b ≠ c := by
  cases b <;> cases c <;> simp [boolComplex]


end Dixmier

end OAI
