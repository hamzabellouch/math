import OAI.Algebra.DepthFive.ConfiguredRankData
import OAI.Algebra.DepthFive.SecondMomentNormalization
import OAI.Algebra.DepthFive.MomentLossParameters

namespace OAI

/-! Exact normalization and uniform numerical losses for the configured second
trace. The actual trace-to-path inequality is deliberately an explicit premise. -/

noncomputable section

namespace Problem335.LowerParameters

open MomentPairing

/-- The path mean for the balanced partition uses exactly the configured
numbers of differentiation and multiplication layers. -/
theorem configured_pathMean_eq {L : ℕ} (hn : 4 ≤ L + 1) :
    pathMean (balancedLayer hn)
      ((a (L + 1) : ℝ) / v (L + 1))
      ((b (L + 1) : ℝ) / u (L + 1)) =
    ((a (L + 1) : ℝ) / v (L + 1)) ^ k (L + 1) *
      (1 + (b (L + 1) : ℝ) / u (L + 1)) ^ m (L + 1) := by
  simp only [pathMean, balancedLayer_card_true, balancedLayer_card_false]
  rw [add_comm ((b (L + 1) : ℝ) / u (L + 1)) 1]

/-- The common first-moment scale is the path count times the path mean. -/
theorem rankMomentScale_eq_pathMean {L : ℕ} (hn : 4 ≤ L + 1) :
    rankMomentScale (L + 1) = ((L + 1 : ℕ) : ℝ) ^ L *
      pathMean (balancedLayer hn)
        ((a (L + 1) : ℝ) / v (L + 1))
        ((b (L + 1) : ℝ) / u (L + 1)) := by
  rw [configured_pathMean_eq]
  simp only [rankMomentScale, Nat.add_sub_cancel, mul_assoc]

/-- The U-layer correction and the balanced-word factor cost at most ten
square-root units in the exponent, without an occupation upper-loss factor. -/
theorem configured_word_loss_le_exp {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    (1 + beta n) ^ m n * Real.exp (8 * Real.sqrt (n : ℝ)) ≤
      Real.exp (10 * Real.sqrt (n : ℝ)) := by
  calc
    _ ≤ Real.exp (2 * Real.sqrt (n : ℝ)) *
        Real.exp (8 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (u_layer_correction_le_exp hn hbeta)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Rearrangement of the actual path normalization, including the square of
its path-count factor. -/
theorem configured_second_scale_identity {L : ℕ} (hn : 4 ≤ L + 1)
    (W : ℝ) :
    rankDimension (L + 1) *
        pathMean (balancedLayer hn)
          ((a (L + 1) : ℝ) / v (L + 1))
          ((b (L + 1) : ℝ) / u (L + 1)) ^ 2 *
        (((L + 1 : ℕ) : ℝ) ^ (2 * L) * W) =
      rankDimension (L + 1) * rankMomentScale (L + 1) ^ 2 * W := by
  rw [rankMomentScale_eq_pathMean hn, Nat.mul_comm 2 L, pow_mul]
  ring

/-- Numerical endpoint consumed by the actual trace-to-relaxed-path assembly.
There is only one source-dimension factor. -/
theorem configured_second_bound_of_path_bound {L : ℕ} (hn : 16 ≤ L + 1)
    (hbeta : beta (L + 1) ≤ 2 / Real.sqrt ((L + 1 : ℕ) : ℝ))
    (T : ℝ)
    (hT : T ≤ rankDimension (L + 1) *
      pathMean (balancedLayer (show 4 ≤ L + 1 by omega))
        ((a (L + 1) : ℝ) / v (L + 1))
        ((b (L + 1) : ℝ) / u (L + 1)) ^ 2 *
      ((1 + beta (L + 1)) ^ m (L + 1) *
        ((L + 1 : ℕ) : ℝ) ^ (2 * L) *
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)))) :
    T ≤ rankDimension (L + 1) * rankMomentScale (L + 1) ^ 2 *
      Real.exp (10 * Real.sqrt ((L + 1 : ℕ) : ℝ)) := by
  have hn4 : 4 ≤ L + 1 := by omega
  have hid := configured_second_scale_identity hn4
    ((1 + beta (L + 1)) ^ m (L + 1) *
      Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ)))
  have hT' : T ≤ rankDimension (L + 1) * rankMomentScale (L + 1) ^ 2 *
      ((1 + beta (L + 1)) ^ m (L + 1) *
        Real.exp (8 * Real.sqrt ((L + 1 : ℕ) : ℝ))) := by
    rw [← hid]
    convert hT using 1; ring
  exact hT'.trans (mul_le_mul_of_nonneg_left
    (configured_word_loss_le_exp hn hbeta)
    (mul_nonneg (rankDimension_nonneg _) (sq_nonneg _)))

/-- A single absolute threshold discharges every numerical premise of the
configured second-moment normalization. -/
theorem exists_second_moment_parameter_cutoff :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      16 ≤ n ∧ beta n ≤ 2 / Real.sqrt (n : ℝ) ∧
        (1 + beta n) ^ m n * Real.exp (8 * Real.sqrt (n : ℝ)) ≤
          Real.exp (10 * Real.sqrt (n : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_q_beta_le_two_div_sqrt
  refine ⟨max N 16, ?_⟩
  intro n hn
  have hn16 : 16 ≤ n := (le_max_right _ _).trans hn
  have hb := (hN n ((le_max_left _ _).trans hn)).2
  exact ⟨hn16, hb, configured_word_loss_le_exp hn16 hb⟩

end Problem335.LowerParameters

end

end OAI
