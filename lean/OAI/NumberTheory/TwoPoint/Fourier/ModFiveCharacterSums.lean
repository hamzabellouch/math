import OAI.NumberTheory.TwoPoint.Fourier.ModFiveLFunctions
import Mathlib.NumberTheory.LSeries.SumCoeff

namespace OAI

/-! Bounded character sums and the exact Abel integral for modulus five.

Periodicity and the vanishing sum over one period give an absolute bound
four, independent of the character and of the cutoff. This is the first
analytic estimate for the three nonprincipal L-functions.
-/

namespace TwoPointCorrelations

open Finset Filter Asymptotics MeasureTheory
open scoped BigOperators Classical Topology

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

lemma modFive_character_shift (χ : DirichletCharacter ℂ 5) (k n : ℕ) :
    χ ((5 * k + n : ℕ) : ZMod 5) = χ (n : ZMod 5) := by
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]

lemma modFive_character_period_sum (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    (∑ n ∈ range 5, χ (n : ZMod 5)) = 0 := by
  have hs := χ.sum_eq_zero_of_ne_one hχ
  rw [sum_zmod_five] at hs
  simpa only [sum_range_succ, sum_range_zero, zero_add,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] using hs

lemma modFive_character_full_periods (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    (k : ℕ) : (∑ n ∈ range (5 * k), χ (n : ZMod 5)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, sum_range_add, ih, zero_add]
      simp_rw [modFive_character_shift]
      exact modFive_character_period_sum χ hχ

/-- A complete number of periods can be removed exactly. -/
lemma modFive_character_prefix_remainder (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (N : ℕ) :
    (∑ n ∈ range N, χ (n : ZMod 5)) =
      ∑ n ∈ range (N % 5), χ (n : ZMod 5) := by
  have hN : N = 5 * (N / 5) + N % 5 := by omega
  conv_lhs => rw [hN, sum_range_add, modFive_character_full_periods χ hχ, zero_add]
  exact sum_congr rfl fun n _ => modFive_character_shift χ (N / 5) n

theorem modFive_character_prefix_norm (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ (n : ZMod 5)‖ ≤ 4 := by
  rw [modFive_character_prefix_remainder χ hχ]
  calc
    _ ≤ ∑ n ∈ range (N % 5), ‖χ (n : ZMod 5)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (N % 5), (1 : ℝ) := sum_le_sum fun n _ => χ.norm_le_one _
    _ = (N % 5 : ℕ) := by simp
    _ ≤ 4 := by exact_mod_cast (show N % 5 ≤ 4 by omega)

lemma modFive_character_Icc_eq (χ : DirichletCharacter ℂ 5) (N : ℕ) :
    (∑ n ∈ Icc 1 N, χ (n : ZMod 5)) = ∑ n ∈ range (N + 1), χ (n : ZMod 5) := by
  rw [Nat.range_succ_eq_Icc_zero]
  have hset : Icc 1 N = Ioc 0 N := by ext n; simp; omega
  rw [hset, ← add_sum_Ioc_eq_sum_Icc (Nat.zero_le N), Nat.cast_zero,
    MulChar.map_zero χ, zero_add]

theorem modFive_character_Icc_norm (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ (n : ZMod 5)‖ ≤ 4 := by
  rw [modFive_character_Icc_eq]
  exact modFive_character_prefix_norm χ hχ (N + 1)

lemma modFive_character_sum_bigO (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    (fun N : ℕ => ∑ n ∈ Icc 1 N, χ (n : ZMod 5)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (0 : ℝ)) := by
  refine isBigO_iff.mpr ⟨4, Eventually.of_forall fun N => ?_⟩
  simpa only [Real.rpow_zero, norm_one, mul_one] using modFive_character_Icc_norm χ hχ N

/-- The exact integral on the initial half-plane. Bounded partial sums will
allow continuation of its right side to the larger half-plane `re s > 0`. -/
theorem modFive_LFunction_Abel (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ n ∈ Icc 1 ⌊t⌋₊, χ (n : ZMod 5)) * (t : ℂ) ^ (-(s + 1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_eq_mul_integral (fun n => χ (n : ZMod 5)) (by norm_num : (0 : ℝ) ≤ 0)
    (by linarith : (0 : ℝ) < s.re) (χ.LSeriesSummable_of_one_lt_re hs)
    (modFive_character_sum_bigO χ hχ)

end TwoPointCorrelations

end OAI
