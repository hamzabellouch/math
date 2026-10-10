import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicGoodScaleFactors
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! # Uniform separation of the selected word-ball radii -/
namespace PolycyclicRecognition

def harmonicRadius (a n : ℕ) : ℕ := a + 16 ^ n

theorem nat_le_sixteen_pow (n : ℕ) : n ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < (16 : ℕ) ^ n := pow_pos (by decide) n
    omega

theorem harmonicRadius_le_two_pow {a n : ℕ} (ha : a ≤ n) :
    harmonicRadius a n ≤ 2 * 16 ^ n := by
  have h := (nat_le_sixteen_pow a).trans (Nat.pow_le_pow_right (by decide) ha)
  dsimp [harmonicRadius]
  omega

theorem harmonicRadius_next_ge_eight {a n : ℕ} (ha : a ≤ n) :
    8 * harmonicRadius a n ≤ harmonicRadius a (n + 1) := by
  have h := (nat_le_sixteen_pow a).trans (Nat.pow_le_pow_right (by decide) ha)
  dsimp [harmonicRadius]
  rw [pow_succ]
  omega

theorem harmonicRadius_double_le {a i j : ℕ} (ha : a ≤ i) (hij : i < j) :
    2 * harmonicRadius a i ≤ harmonicRadius a j := by
  have hi := harmonicRadius_le_two_pow ha
  have hj := Nat.pow_le_pow_right (by decide : 0 < 16) hij
  rw [pow_succ] at hj
  dsimp [harmonicRadius] at *
  omega

theorem exists_harmonic_separation_width (C : ℝ) :
    ∃ w : ℕ, 0 < w ∧ 4 * C < (16 : ℝ) ^ (2 * w) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (4 * C) (by norm_num : (1 : ℝ) < 256)
  refine ⟨n + 1, by omega, ?_⟩
  have hm : (256 : ℝ) ^ n ≤ 256 ^ (n + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  convert hn.trans_le hm using 1
  rw [pow_mul]
  norm_num

theorem harmonicRadius_quadratic_separation {a i j w : ℕ} (ha : a ≤ i)
    (hij : i + w ≤ j) (C : ℝ) (hC : 0 ≤ C)
    (hwidth : 4 * C < (16 : ℝ) ^ (2 * w)) :
    C * (harmonicRadius a i : ℝ) ^ 2 < (harmonicRadius a j : ℝ) ^ 2 := by
  have hi : (harmonicRadius a i : ℝ) ≤ 2 * (16 : ℝ) ^ i := by
    exact_mod_cast harmonicRadius_le_two_pow ha
  have hj : (16 : ℝ) ^ i * 16 ^ w ≤ (harmonicRadius a j : ℝ) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 16) hij
    rw [pow_add] at h
    exact_mod_cast h.trans (Nat.le_add_left _ _)
  calc
    _ ≤ C * (2 * (16 : ℝ) ^ i) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 2) hC
    _ = (4 * C) * ((16 : ℝ) ^ i) ^ 2 := by ring
    _ < (16 : ℝ) ^ (2 * w) * ((16 : ℝ) ^ i) ^ 2 :=
      mul_lt_mul_of_pos_right hwidth (by positivity)
    _ = ((16 : ℝ) ^ i * 16 ^ w) ^ 2 := by rw [mul_comm 2 w, pow_mul]; ring
    _ ≤ (harmonicRadius a j : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hj 2

end PolycyclicRecognition

end OAI
