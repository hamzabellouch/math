import OAI.Geometry.PeriodicTiling.FinitePairCounting
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Power

namespace OAI

universe uV uC

namespace PeriodicTilingThree

open scoped Classical

theorem allBadAssignments_card_ratio_le {V : Type uV} {C : Type uC} [Fintype V] [Fintype C]
    {k : ℕ} (pair : (Fin k × Fin 2) ↪ V) (Good : Fin k → Finset (C × C))
    (g : ℕ) (hC : 0 < Fintype.card C) (hgB : g ≤ Fintype.card C ^ 2)
    (hgood : ∀ j, g ≤ (Good j).card) :
    ((allBadAssignments pair Good).card : ℚ) / (Fintype.card (V → C) : ℚ) ≤
      (1 - (g : ℚ) / (Fintype.card C : ℚ) ^ 2) ^ k := by
  let B : ℚ := Fintype.card C
  let N : ℕ := Fintype.card V
  have hBpos : 0 < B := Nat.cast_pos.mpr hC
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hdim : 2 * k ≤ N := by
    have h := Fintype.card_le_of_embedding pair
    simpa only [Fintype.card_prod, Fintype.card_fin, mul_comm, N] using h
  have hcast : ((allBadAssignments pair Good).card : ℚ) ≤
      (B ^ 2 - (g : ℚ)) ^ k * B ^ (N - 2 * k) := by
    have h := (Nat.cast_le (α := ℚ)).mpr
      (allBadAssignments_card_le pair Good g hgood)
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hgB, B, N] using h
  have hsplit : B ^ N = (B ^ 2) ^ k * B ^ (N - 2 * k) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_of_le hdim]
  rw [Fintype.card_fun, Nat.cast_pow]
  change ((allBadAssignments pair Good).card : ℚ) / B ^ N ≤
    (1 - (g : ℚ) / B ^ 2) ^ k
  calc
    ((allBadAssignments pair Good).card : ℚ) / B ^ N
        ≤ ((B ^ 2 - (g : ℚ)) ^ k * B ^ (N - 2 * k)) / B ^ N :=
      div_le_div_of_nonneg_right hcast (pow_pos hBpos N).le
    _ = (B ^ 2 - (g : ℚ)) ^ k / (B ^ 2) ^ k := by
      rw [hsplit]
      exact mul_div_mul_right _ _ (pow_ne_zero _ hBne)
    _ = ((B ^ 2 - (g : ℚ)) / B ^ 2) ^ k := (div_pow _ _ _).symm
    _ = (1 - (g : ℚ) / B ^ 2) ^ k := by
      rw [sub_div, div_self (pow_ne_zero _ hBne)]

end PeriodicTilingThree

end OAI
