import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphSequence
import Mathlib.Topology.Algebra.InfiniteSum.Module

namespace OAI

/-! # The convergent backward sum in the graph construction

The inverse unstable evolution only needs operator norm at most one.  The
factor `2⁻ʲ` from the weighted sequence space supplies summability, including
the neutral phase coordinate.  The bound is exactly the geometric cost two.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem stableBackward_term_bound (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f : ℕ →ᵇ E) (n j : ℕ) :
    ‖(1 / 2 : ℝ) ^ j • (R ^ (j + 1)) (f (n + j))‖ ≤
      (1 / 2 : ℝ) ^ j * ‖f‖ := by
  have hpow_all (i : ℕ) : ‖R ^ i‖ ≤ 1 := by
    induction i with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
    | succ i hi =>
        calc
          ‖R ^ (i + 1)‖ ≤ ‖R ^ i‖ * ‖R‖ := by rw [pow_succ]; exact norm_mul_le _ _
          _ ≤ 1 * 1 := mul_le_mul hi hR (norm_nonneg _) (by norm_num)
          _ = 1 := one_mul _
  have hpow := hpow_all (j + 1)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖(R ^ (j + 1)) (f (n + j))‖ ≤ ‖R ^ (j + 1)‖ * ‖f (n + j)‖ :=
      (R ^ (j + 1)).le_opNorm _
    _ ≤ 1 * ‖f‖ := mul_le_mul hpow (f.norm_coe_le_norm _) (norm_nonneg _) (by norm_num)
    _ = ‖f‖ := one_mul _

theorem stableBackward_summable (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f : ℕ →ᵇ E) (n : ℕ) :
    Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j • (R ^ (j + 1)) (f (n + j))) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right ‖f‖)
  exact stableBackward_term_bound R hR f n

theorem stableBackward_sum_bound (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f : ℕ →ᵇ E) (n : ℕ) :
    ‖∑' j : ℕ, (1 / 2 : ℝ) ^ j • (R ^ (j + 1)) (f (n + j))‖ ≤ 2 * ‖f‖ := by
  have hs : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ j * ‖f‖) (2 * ‖f‖) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right ‖f‖ using 1
    norm_num
  exact (stableBackward_summable R hR f n).hasSum.norm_le_of_bounded hs
    (stableBackward_term_bound R hR f n)

/-- Negative backward solution of the normalized unstable recurrence. -/
noncomputable def stableBackward (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f : ℕ →ᵇ E) : ℕ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => -(∑' j : ℕ, (1 / 2 : ℝ) ^ j • (R ^ (j + 1)) (f (n + j))))
    (2 * ‖f‖) (fun n => by simpa using stableBackward_sum_bound R hR f n)

theorem stableBackward_apply (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f : ℕ →ᵇ E) (n : ℕ) :
    stableBackward R hR f n = -(∑' j : ℕ, (1 / 2 : ℝ) ^ j •
      (R ^ (j + 1)) (f (n + j))) := rfl

theorem norm_stableBackward_le (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f : ℕ →ᵇ E) : ‖stableBackward R hR f‖ ≤ 2 * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro n
  simpa only [stableBackward_apply, norm_neg] using stableBackward_sum_bound R hR f n

theorem stableBackward_sub (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f g : ℕ →ᵇ E) :
    stableBackward R hR (f - g) = stableBackward R hR f - stableBackward R hR g := by
  apply BoundedContinuousFunction.ext
  intro n
  simp only [stableBackward_apply, BoundedContinuousFunction.sub_apply, map_sub, smul_sub]
  rw [(stableBackward_summable R hR f n).tsum_sub (stableBackward_summable R hR g n)]
  abel

theorem stableBackward_dist_le (R : E →L[ℝ] E) (hR : ‖R‖ ≤ 1)
    (f g : ℕ →ᵇ E) :
    dist (stableBackward R hR f) (stableBackward R hR g) ≤ 2 * dist f g := by
  simpa only [dist_eq_norm, stableBackward_sub] using norm_stableBackward_le R hR (f - g)

end DefocusingNLS

end OAI
