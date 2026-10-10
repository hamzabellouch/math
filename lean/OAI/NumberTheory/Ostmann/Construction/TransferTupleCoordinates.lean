import OAI.NumberTheory.Ostmann.Construction.TransferGraphRows

namespace OAI

/-! # Exact product and cofactor coordinates for the copied prime list -/

namespace Ostmann

open scoped BigOperators

theorem transferredLabels_prod {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) :
    (∏ i, transferredLabels L R U i) = (∏ h, L h) * (∏ h, R h) * (∏ y, U y) := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool]
  rfl

theorem tupleCofactor_sum_left {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) (h : H) (hL : L h ≠ 0) :
    tupleCofactor (Sum.elim L U) (.inl h) = tupleCofactor L h * ∏ y, U y := by
  apply mul_left_cancel₀ hL
  calc
    _ = ∏ i, Sum.elim L U i := tupleCofactor_mul (Sum.elim L U) (.inl h)
    _ = (∏ k, L k) * ∏ y, U y := Fintype.prod_sum_type _
    _ = (L h * tupleCofactor L h) * ∏ y, U y := by rw [tupleCofactor_mul]
    _ = _ := by ring

theorem tupleCofactor_sum_right {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) (y : Y) (hU : U y ≠ 0) :
    tupleCofactor (Sum.elim L U) (.inr y) = (∏ h, L h) * tupleCofactor U y := by
  apply mul_left_cancel₀ hU
  calc
    _ = ∏ i, Sum.elim L U i := tupleCofactor_mul (Sum.elim L U) (.inr y)
    _ = (∏ k, L k) * ∏ y, U y := Fintype.prod_sum_type _
    _ = (∏ k, L k) * (U y * tupleCofactor U y) := by rw [tupleCofactor_mul]
    _ = _ := by ring

theorem tupleCofactor_transferred_left {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (h : H) (hL : L h ≠ 0) :
    tupleCofactor (transferredLabels L R U) (.inl (true, h)) =
      tupleCofactor L h * (∏ k, R k) * ∏ y, U y := by
  apply mul_left_cancel₀ hL
  calc
    _ = ∏ i, transferredLabels L R U i := tupleCofactor_mul _ (.inl (true, h))
    _ = (∏ k, L k) * (∏ k, R k) * ∏ y, U y := transferredLabels_prod L R U
    _ = (L h * tupleCofactor L h) * (∏ k, R k) * ∏ y, U y := by rw [tupleCofactor_mul]
    _ = _ := by ring

theorem tupleCofactor_transferred_right {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (h : H) (hR : R h ≠ 0) :
    tupleCofactor (transferredLabels L R U) (.inl (false, h)) =
      (∏ k, L k) * tupleCofactor R h * ∏ y, U y := by
  apply mul_left_cancel₀ hR
  calc
    _ = ∏ i, transferredLabels L R U i := tupleCofactor_mul _ (.inl (false, h))
    _ = (∏ k, L k) * (∏ k, R k) * ∏ y, U y := transferredLabels_prod L R U
    _ = (∏ k, L k) * (R h * tupleCofactor R h) * ∏ y, U y := by rw [tupleCofactor_mul]
    _ = _ := by ring

theorem tupleCofactor_transferred_outside {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (y : Y) (hU : U y ≠ 0) :
    tupleCofactor (transferredLabels L R U) (.inr y) =
      (∏ h, L h) * (∏ h, R h) * tupleCofactor U y := by
  apply mul_left_cancel₀ hU
  calc
    _ = ∏ i, transferredLabels L R U i := tupleCofactor_mul _ (.inr y)
    _ = (∏ k, L k) * (∏ k, R k) * ∏ y, U y := transferredLabels_prod L R U
    _ = (∏ k, L k) * (∏ k, R k) * (U y * tupleCofactor U y) := by rw [tupleCofactor_mul]
    _ = _ := by ring

end Ostmann

end OAI
