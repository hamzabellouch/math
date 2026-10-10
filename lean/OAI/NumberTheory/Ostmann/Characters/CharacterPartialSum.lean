import Mathlib.NumberTheory.LSeries.SumCoeff
import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedComplexZeroDensity

namespace OAI

/-! # Elementary cancellation in primitive nonprincipal character sums

These concrete prefix bounds are the first step in the remaining analytic
zero-count and explicit-formula obligations.
-/

namespace Ostmann

open Finset Filter
open scoped Classical BigOperators

theorem PrimitiveComplexCharacter.period_sum (χ : PrimitiveComplexCharacter) :
    (∑ n ∈ range χ.modulus, χ.character (n : ZMod χ.modulus)) = 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hsum : (∑ n ∈ range χ.modulus, χ.character (n : ZMod χ.modulus)) =
      ∑ a : ZMod χ.modulus, χ.character a := by
    apply sum_bij (t := (univ : Finset (ZMod χ.modulus)))
      (fun (n : ℕ) _ => (n : ZMod χ.modulus))
    · intro n hn
      exact mem_univ _
    · intro n hn m hm he
      have h := congrArg ZMod.val he
      simpa only [ZMod.val_natCast_of_lt (mem_range.mp hn),
        ZMod.val_natCast_of_lt (mem_range.mp hm)] using h
    · intro a ha
      exact ⟨a.val, mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
    · intro n hn
      rfl
  rw [hsum]
  exact MulChar.sum_eq_zero_of_ne_one χ.nontrivial

theorem PrimitiveComplexCharacter.period_blocks_sum (χ : PrimitiveComplexCharacter) (k : ℕ) :
    (∑ n ∈ range (k * χ.modulus), χ.character (n : ZMod χ.modulus)) = 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, zero_add]
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
      using χ.period_sum

theorem PrimitiveComplexCharacter.prefix_remainder (χ : PrimitiveComplexCharacter) (N : ℕ) :
    (∑ n ∈ range N, χ.character (n : ZMod χ.modulus)) =
      ∑ n ∈ range (N % χ.modulus), χ.character (n : ZMod χ.modulus) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hN : N = (N / χ.modulus) * χ.modulus + N % χ.modulus := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  conv_lhs => rw [hN]
  rw [sum_range_add, χ.period_blocks_sum, zero_add]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

theorem PrimitiveComplexCharacter.prefix_bound (χ : PrimitiveComplexCharacter) (N : ℕ) :
    ‖∑ n ∈ range N, χ.character (n : ZMod χ.modulus)‖ ≤ χ.modulus := by
  rw [χ.prefix_remainder]
  calc
    _ ≤ ∑ n ∈ range (N % χ.modulus), ‖χ.character (n : ZMod χ.modulus)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (N % χ.modulus), (1 : ℝ) := sum_le_sum (fun _ _ => χ.character.norm_le_one _)
    _ = (N % χ.modulus : ℕ) := by simp
    _ ≤ (χ.modulus : ℝ) := by exact_mod_cast (Nat.mod_lt N χ.positive).le

theorem PrimitiveComplexCharacter.prefix_Icc_bound (χ : PrimitiveComplexCharacter) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ.character (n : ZMod χ.modulus)‖ ≤ χ.modulus + 1 := by
  have he : (∑ n ∈ range (N + 1), χ.character (n : ZMod χ.modulus)) =
      χ.character 0 + ∑ n ∈ Icc 1 N, χ.character (n : ZMod χ.modulus) := by
    rw [Nat.range_succ_eq_Icc_zero,
      ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), sum_insert (by simp)]
    simp
  have hb := χ.prefix_bound (N + 1)
  have hn := norm_sub_le (∑ n ∈ range (N + 1), χ.character (n : ZMod χ.modulus)) (χ.character 0)
  rw [he] at hn hb
  simpa only [add_sub_cancel_left] using hn.trans
    (add_le_add hb (χ.character.norm_le_one 0))

end Ostmann

end OAI
