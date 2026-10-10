import Mathlib

namespace OAI

/-! Moser Iteration. -/

noncomputable section
open Filter Finset Topology
namespace Anticanonical.SourceSmooth

theorem moser_sequence_bound (ν C a : ℝ) (hν : 1 < ν) (hC : 0 < C)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hstep : ∀ n, u (n+1) ≤ (C*(a*ν^n)^2) ^ (1/(a*ν^n)) * u n)
    (ha : 0 < a) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, u n ≤ B * u 0 := by
  let b : ℕ → ℝ := fun n => (Real.log C + 2*Real.log a + 2*(n:ℝ)*Real.log ν) / (a*ν^n)
  have hν0 : 0 < ν := lt_trans zero_lt_one hν
  have hb (n : ℕ) : (C*(a*ν^n)^2) ^ (1/(a*ν^n)) = Real.exp (b n) := by
    rw [Real.rpow_def_of_pos (mul_pos hC (sq_pos_of_pos (mul_pos ha (pow_pos hν0 _)) ))]
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (sq_pos_of_pos (mul_pos ha (pow_pos hν0 _)))),
      Real.log_pow, Real.log_mul (ne_of_gt ha) (ne_of_gt (pow_pos hν0 _)), Real.log_pow]
    congr 1; dsimp [b]; ring
  have hs : Summable b := by
    have hi : |ν⁻¹| < 1 := by rw [abs_of_pos (inv_pos.mpr hν0)]; exact inv_lt_one_of_one_lt₀ hν
    have hg := summable_geometric_of_abs_lt_one hi
    have hn : Summable (fun n : ℕ => (n:ℝ)*ν⁻¹^n) := by
      simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖ν⁻¹‖ < 1 by simpa only [Real.norm_eq_abs] using hi)
    apply (((hg.mul_left (Real.log C + 2*Real.log a)).add (hn.mul_left (2*Real.log ν))).div_const a).congr
    intro n
    dsimp only [b]
    simp only [inv_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  have hsabs := hs.abs
  refine ⟨Real.exp (∑' n, |b n|), (Real.exp_pos _).le, ?_⟩
  have hind (n : ℕ) : u n ≤ Real.exp (∑ k ∈ range n, b k) * u 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        u (n+1) ≤ Real.exp (b n) * u n := by simpa only [hb] using hstep n
        _ ≤ Real.exp (b n) * (Real.exp (∑ k ∈ range n, b k) * u 0) := mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = _ := by rw [sum_range_succ, Real.exp_add]; ring
  intro n
  apply (hind n).trans
  apply mul_le_mul_of_nonneg_right _ (hu 0)
  apply Real.exp_le_exp.mpr
  calc
    ∑ k ∈ range n, b k ≤ ∑ k ∈ range n, |b k| := sum_le_sum (fun _ _ => le_abs_self _)
    _ ≤ ∑' k, |b k| := Summable.sum_le_tsum (range n) (fun k _ => abs_nonneg (b k)) hsabs

end Anticanonical.SourceSmooth

end

end OAI
