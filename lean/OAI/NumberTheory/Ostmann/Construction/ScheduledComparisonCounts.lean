import OAI.NumberTheory.Ostmann.Construction.ScheduledComparisonCutoffs
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTemplate

namespace OAI

/-! # Complexity of the actual bounded cell schedule and spectator list -/
namespace Ostmann
open Filter

noncomputable def scheduledComparisonCount (k m : ℕ) : ℕ :=
  2 + 2 ^ k * (10 + 4 * k + m) + 4 * k * 2 ^ k + m

theorem scheduled_comparison_count (k n r m : ℕ) (hn : n ≤ k) (hr : r ≤ 10 + 4 * k)
    (D : Finset ℕ) (outside : List ℕ) (hD : D.card ≤ 2) (hout : outside.length ≤ m) :
    D.card + (Fintype.card (MovingRegularSlot n r m) + 4 * n * 2 ^ n) + outside.length ≤
      scheduledComparisonCount k m := by
  have hp : 2 ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hn
  have hslot := Nat.mul_le_mul hp (Nat.add_le_add_right hr m)
  have hi := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hn) hp
  rw [movingRegularSlot_card]
  unfold scheduledComparisonCount
  omega

theorem eventual_scheduled_comparison_count (k : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (scheduledComparisonCount k (spectatorBulkCount k L) : ℝ) ≤ Real.exp (3 * L) := by
  let X : ℝ := 2 + (2 : ℝ) ^ k * (10 + 4 * k) + 4 * k * (2 : ℝ) ^ k
  let Y : ℝ := (2 : ℝ) ^ k + 1
  let C := X + Y * (k : ℝ) ^ 4
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  filter_upwards [arithmetic_exponent_absorption 0 3 0 C 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hbound hL
  have hm := spectatorBulkCount_upper k L (by linarith)
  have hn : (scheduledComparisonCount k (spectatorBulkCount k L) : ℝ) =
      X + Y * spectatorBulkCount k L := by
    simp only [scheduledComparisonCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only [X, Y]
    ring
  have hCL : C * L ≤ Real.exp (3 * L) := by
    simp only [pow_zero, zero_mul, Real.exp_zero, mul_one, one_mul] at hbound
    linarith
  rw [hn]
  apply le_trans _ hCL
  calc
    _ ≤ X * L + Y * ((k : ℝ) ^ 4 * L) :=
      add_le_add (le_mul_of_one_le_right hX hL) (mul_le_mul_of_nonneg_left hm hY)
    _ = _ := by dsimp only [C]; ring

end Ostmann

end OAI
