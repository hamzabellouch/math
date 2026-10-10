import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphBackward
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! # An explicit bound on the initial finite coordinate of a decaying orbit -/

open Filter Topology

namespace DefocusingNLS

theorem stableCoordinate_initial_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : F →L[ℝ] F) (hR : ‖R‖ ≤ 1)
    (u f : ℕ → F) (B E : ℝ) (hE : 0 ≤ E)
    (hu : ∀ n, ‖u n‖ ≤ B * (1 / 2 : ℝ) ^ n)
    (hf : ∀ n, ‖f n‖ ≤ E * (1 / 2 : ℝ) ^ n)
    (hrec : ∀ n, u n = R (u (n + 1) - f n)) :
    ‖u 0‖ ≤ 2 * E := by
  have hs (n : ℕ) : ‖u n‖ ≤ ‖u (n + 1)‖ + ‖f n‖ := by
    rw [hrec n]
    have hb : ‖R (u (n + 1) - f n)‖ ≤ ‖u (n + 1) - f n‖ := by
      simpa only [one_mul] using R.le_of_opNorm_le hR (u (n + 1) - f n)
    exact hb.trans (norm_sub_le _ _)
  have ht (n : ℕ) : ‖u 0‖ ≤ ‖u n‖ + ∑ j ∈ Finset.range n, ‖f j‖ := by
    induction n with
    | zero => simp
    | succ n hn =>
        rw [Finset.sum_range_succ]
        linarith [hs n]
  have hg : HasSum (fun n : ℕ => E * (1 / 2 : ℝ) ^ n) (2 * E) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left E using 1
    ring
  have hb (n : ℕ) : ‖u 0‖ ≤ B * (1 / 2 : ℝ) ^ n + 2 * E := by
    apply (ht n).trans
    apply add_le_add (hu n)
    calc
      (∑ j ∈ Finset.range n, ‖f j‖) ≤ ∑ j ∈ Finset.range n, E * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum (fun j _ => hf j)
      _ ≤ 2 * E := by
        rw [← hg.tsum_eq]
        exact hg.summable.sum_le_tsum _ (fun j _ => mul_nonneg hE (by positivity))
  have hl : Tendsto (fun n : ℕ => B * (1 / 2 : ℝ) ^ n + 2 * E) atTop (𝓝 (2 * E)) := by
    simpa only [mul_zero, zero_add] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul B).add_const (2 * E)
  exact ge_of_tendsto hl (Eventually.of_forall hb)

end DefocusingNLS

end OAI
