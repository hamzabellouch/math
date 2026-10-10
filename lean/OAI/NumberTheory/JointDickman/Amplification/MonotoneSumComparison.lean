import Mathlib

namespace OAI

/-! # Decreasing weights preserve domination of partial sums -/
namespace JointDickman
open Finset

lemma antitone_weighted_sum_nonpos (f w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hanti : Antitone w)
    (hf : ∀ k ≤ N, (∑ i ∈ range k, f i) ≤ 0) :
    (∑ i ∈ range N, w i*f i) ≤ 0 := by
  cases N with
  | zero => simp
  | succ N =>
    rw [show (∑ i ∈ range (N+1), w i*f i) = ∑ i ∈ range (N+1), w i • f i by simp]
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel,smul_eq_mul]
    have hfirst : w N*(∑ i ∈ range (N+1), f i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hw N) (hf _ le_rfl)
    have hsecond : 0 ≤ ∑ i ∈ range N, (w (i+1)-w i)*(∑ j ∈ range (i+1), f j) := by
      apply sum_nonneg
      intro i hi
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hanti (by omega))) (hf _ (by have := mem_range.mp hi; omega))
    linarith

lemma antitone_weighted_sum_le (f g w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hanti : Antitone w)
    (hfg : ∀ k ≤ N, (∑ i ∈ range k, f i) ≤ ∑ i ∈ range k, g i) :
    (∑ i ∈ range N, w i*f i) ≤ ∑ i ∈ range N, w i*g i := by
  have h := antitone_weighted_sum_nonpos (fun i => f i-g i) w N hw hanti (by
    intro k hk
    simpa only [sum_sub_distrib,sub_nonpos] using hfg k hk)
  simpa only [mul_sub,sum_sub_distrib,sub_nonpos] using h

end JointDickman

end OAI
