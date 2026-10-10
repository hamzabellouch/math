import OAI.NumberTheory.JointDickman.Probability.AmplificationHighCoins
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! # The finite dyadic decomposition by the largest changed prime -/

namespace JointDickman

open Finset

/-- One dyadic upper endpoint covers a fixed positive interval, with at
most a factor-two overshoot. -/
theorem dyadic_cover_endpoint {L X : ℝ} (hL : 0 < L) (hLX : L ≤ X) :
    ∃ N : ℕ, 0 < N ∧ X ≤ (2 : ℝ)^N * L ∧ (2 : ℝ)^N * L ≤ 2 * X := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_div hL).mpr hLX) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · exact ((div_lt_iff₀ hL).mp hn').le
  · rw [pow_succ]
    have hh := (le_div_iff₀ hL).mp hn
    linarith only [hh]

/-- Every changed logarithm above the cutoff belongs to an actual dyadic
shell, including equality at an upper endpoint. -/
theorem dyadic_shell_cover {L x : ℝ} {N : ℕ} (_hL : 0 < L) (hx : L < x)
    (hcap : x ≤ (2 : ℝ)^N * L) :
    ∃ i ∈ Icc 1 N, ((2 : ℝ)^i * L) / 2 < x ∧ x ≤ (2 : ℝ)^i * L := by
  have hex : ∃ i : ℕ, x ≤ (2 : ℝ)^i * L := ⟨N, hcap⟩
  let i := Nat.find hex
  have hi : x ≤ (2 : ℝ)^i * L := Nat.find_spec hex
  have hiN : i ≤ N := Nat.find_min' hex hcap
  have hi0 : 0 < i := by
    by_contra h
    have hz : i = 0 := by omega
    rw [hz, pow_zero, one_mul] at hi
    linarith only [hx, hi]
  refine ⟨i, mem_Icc.mpr ⟨hi0, hiN⟩, ?_, hi⟩
  have hprev : ¬ x ≤ (2 : ℝ)^(i - 1) * L := Nat.find_min hex (by omega)
  have heq : ((2 : ℝ)^i * L) / 2 = (2 : ℝ)^(i - 1) * L := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi0)
    rw [hj]
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  rw [heq]
  exact lt_of_not_ge hprev

/-- No overlap occurs between distinct dyadic shells. -/
theorem dyadic_shell_unique {L x : ℝ} {i j : ℕ} (hL : 0 < L)
    (hi : ((2 : ℝ)^i * L) / 2 < x ∧ x ≤ (2 : ℝ)^i * L)
    (hj : ((2 : ℝ)^j * L) / 2 < x ∧ x ≤ (2 : ℝ)^j * L) : i = j := by
  have hle {m n : ℕ} (hmn : m < n) : (2 : ℝ)^m * L ≤ ((2 : ℝ)^n * L) / 2 := by
    have hp : (2 : ℝ)^(m + 1) ≤ (2 : ℝ)^n := pow_le_pow_right₀ (by norm_num) hmn
    rw [pow_succ] at hp
    nlinarith only [mul_le_mul_of_nonneg_right hp hL.le]
  rcases lt_trichotomy i j with h | h | h
  · have hh := hle h
    linarith only [hh, hi.2, hj.1]
  · exact h
  · have hh := hle h
    linarith only [hh, hj.2, hi.1]

end JointDickman

end OAI
