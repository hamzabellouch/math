import Mathlib

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.ZeroMoment

theorem geometric_sum_le {B : ℝ} (hB : 2 ≤ B) (e : ℕ) :
    ∑ j ∈ Finset.range (e + 1), B ^ j ≤ 2 * B ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hp : 0 ≤ B ^ e := pow_nonneg (by linarith) _
      nlinarith

theorem diagonal_sum_le {B : ℝ} (hB : 2 ≤ B) (b e : ℕ) :
    ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) ≤
      2 * B ^ (b + e) := by
  have hB1 : 1 ≤ B := by linarith
  calc
    ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) ≤
        ∑ j ∈ Finset.range (e + 1), B ^ (b + j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_right₀ hB1 (by omega)
    _ = B ^ b * ∑ j ∈ Finset.range (e + 1), B ^ j := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ B ^ b * (2 * B ^ e) :=
      mul_le_mul_of_nonneg_left (geometric_sum_le hB e) (by positivity)
    _ = 2 * B ^ (b + e) := by rw [pow_add]; ring

theorem cubic_moment_of_tail {α : Type*} [DecidableEq α]
    (S : Finset α) (v : α → ℕ) {B A : ℝ} (b e : ℕ)
    (hB : 2 ≤ B) (hA : 0 ≤ A)
    (hv : ∀ x ∈ S, v x ≤ e)
    (htail : ∀ j ≤ e,
      ((S.filter fun x => j ≤ v x).card : ℝ) ≤ A / B ^ (j + (j - b))) :
    ∑ x ∈ S, B ^ (3 * v x) ≤ 2 * A * B ^ (b + e) := by
  have hB0 : 0 < B := by linarith
  have hterm (x : α) (hx : x ∈ S) :
      B ^ (3 * v x) ≤ ∑ j ∈ Finset.range (e + 1),
        if j ≤ v x then B ^ (3 * j) else 0 := by
    have hmem : v x ∈ Finset.range (e + 1) := by
      simpa using Nat.lt_succ_of_le (hv x hx)
    simpa using Finset.single_le_sum
      (f := fun j => if j ≤ v x then B ^ (3 * j) else 0)
      (fun j hj => by split_ifs <;> positivity) hmem
  calc
    ∑ x ∈ S, B ^ (3 * v x) ≤
        ∑ x ∈ S, ∑ j ∈ Finset.range (e + 1),
          if j ≤ v x then B ^ (3 * j) else 0 :=
      Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range (e + 1),
        B ^ (3 * j) * ((S.filter fun x => j ≤ v x).card : ℝ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ ≤ ∑ j ∈ Finset.range (e + 1),
        B ^ (3 * j) * (A / B ^ (j + (j - b))) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left (htail j (by simpa using hj))
      positivity
    _ = A * ∑ j ∈ Finset.range (e + 1), B ^ (2 * j - (j - b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have he : 3 * j - (j + (j - b)) = 2 * j - (j - b) := by omega
      rw [← he, pow_sub₀ B hB0.ne' (by omega)]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ A * (2 * B ^ (b + e)) :=
      mul_le_mul_of_nonneg_left (diagonal_sum_le hB b e) hA
    _ = 2 * A * B ^ (b + e) := by ring

end Problem355.ZeroMoment

end

end OAI
