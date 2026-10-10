import Mathlib

namespace OAI

/-! # Finite partial summation with decreasing nonnegative weights -/
namespace JointDickman
open Finset

lemma monotone_weighted_sum_range_bound (g : ℕ → ℂ) (w : ℕ → ℝ)
    {N : ℕ} {D : ℝ} (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i)
    (hanti : Antitone w)
    (hpartial : ∀ k ≤ N, ‖∑ i ∈ range k, g i‖ ≤ D) :
    ‖∑ i ∈ range N, w i • g i‖ ≤ D * w 0 := by
  have htel (M : ℕ) : (∑ i ∈ range M, (w i-w (i+1))) = w 0-w M := by
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; ring
  cases N with
  | zero => simpa using mul_nonneg hD (hw 0)
  | succ N =>
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel]
    have hterm : ‖w N • (∑ i ∈ range (N+1), g i)‖ ≤ w N * D := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw N)]
      exact mul_le_mul_of_nonneg_left (hpartial _ le_rfl) (hw N)
    have hsum : ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ ≤
        (∑ i ∈ range N, (w i-w (i+1))) * D := by
      calc
        _ ≤ ∑ i ∈ range N, ‖(w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ range N, (w i-w (i+1))*D := by
          apply sum_le_sum
          intro i hi
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hanti (by omega)))]
          have hiN : i < N := mem_range.mp hi
          nlinarith [hpartial (i+1) (by omega), hanti (show i ≤ i+1 by omega)]
        _ = _ := (sum_mul ..).symm
    calc
      _ ≤ ‖w N • (∑ i ∈ range (N+1), g i)‖ +
          ‖∑ i ∈ range N, (w (i+1)-w i) • (∑ j ∈ range (i+1), g j)‖ := norm_sub_le _ _
      _ ≤ w N*D+(∑ i ∈ range N, (w i-w (i+1)))*D := add_le_add hterm hsum
      _ = D*w 0 := by rw [htel]; ring

end JointDickman

end OAI
