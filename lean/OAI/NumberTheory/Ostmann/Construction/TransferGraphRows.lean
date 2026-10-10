import OAI.NumberTheory.Ostmann.Construction.TransferGraph
import OAI.NumberTheory.Ostmann.Construction.TransferRowProducts

namespace OAI

/-! # The row products of the actual transferred directed graph -/

namespace Ostmann

open scoped BigOperators

def transferredLabels {H Y K : Type*} (L R : H → K) (U : Y → K) : (Bool × H) ⊕ Y → K
  | .inl (true, h) => L h
  | .inl (false, h) => R h
  | .inr y => U y

/-- This is the full left row, including the harmless zero diagonal
exponent. The cross-copy row is exactly the old incoming pivot column. -/
theorem transferredGraph_left_row {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (L R : H → ZMod p) (U : Y → ZMod p) (h : H) :
    (∏ j, χ (transferredLabels L R U j) ^ transferredGraph b (.inl (true, h)) j) =
      (∏ k, χ (L k) ^ b (some (.inl h)) (some (.inl k))) *
      (∏ k, χ (R k) ^ b (some (.inl h)) none) *
      (∏ y, χ (U y) ^ b (some (.inl h)) (some (.inr y))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [transferredLabels, transferredGraph, transferCopySign, ite_true,
    Bool.true_eq_false, ite_false, one_mul]

/-- The conjugated right row has precisely the negated same-copy and
incoming-pivot exponents. -/
theorem transferredGraph_right_row {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (L R : H → ZMod p) (U : Y → ZMod p) (h : H) :
    (∏ j, χ (transferredLabels L R U j) ^ transferredGraph b (.inl (false, h)) j) =
      (∏ k, χ (L k) ^ (-b (some (.inl h)) none)) *
      (∏ k, χ (R k) ^ (-b (some (.inl h)) (some (.inl k)))) *
      (∏ y, χ (U y) ^ (-b (some (.inl h)) (some (.inr y)))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [transferredLabels, transferredGraph, transferCopySign, ite_true,
    Bool.false_eq_true, ite_false, neg_one_mul]

/-- Shared outside rows lose every shared-to-shared edge. -/
theorem transferredGraph_outside_row {H Y : Type*} [Fintype H] [Fintype Y]
    {p : ℕ} (χ : DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (L R : H → ZMod p) (U : Y → ZMod p) (y : Y) :
    (∏ j, χ (transferredLabels L R U j) ^ transferredGraph b (.inr y) j) =
      (∏ k, χ (L k) ^ b (some (.inr y)) (some (.inl k))) *
      (∏ k, χ (R k) ^ (-b (some (.inr y)) (some (.inl k)))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [transferredLabels, transferredGraph, transferCopySign, ite_true,
    Bool.false_eq_true, ite_false, one_mul, neg_one_mul, zpow_zero, Finset.prod_const_one, mul_one]

end Ostmann

end OAI
