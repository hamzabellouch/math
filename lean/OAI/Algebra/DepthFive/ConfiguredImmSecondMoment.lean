import OAI.Algebra.DepthFive.ImmSecondMomentParameters
import OAI.Algebra.DepthFive.ActualRelaxedWeightBound
import OAI.Algebra.DepthFive.ActualImmRank
import OAI.Algebra.DepthFive.ActualSecondMomentParameters

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335.LowerParameters
open MomentPairing

private theorem configured_layerMeanV {L : ℕ} (hn : 4 ≤ L + 1) :
    layerMeanV (Fin (L + 1)) (balancedLayer hn) (a (L + 1)) =
      (a (L + 1) : ℝ) / v (L + 1) := by
  unfold layerMeanV
  rw [balancedVariable_card_true hn]

private theorem configured_layerMeanU {L : ℕ} (hn : 4 ≤ L + 1) :
    layerMeanU (Fin (L + 1)) (balancedLayer hn) (b (L + 1)) =
      (b (L + 1) : ℝ) / u (L + 1) := by
  unfold layerMeanU
  simp only [Bool.not_eq_true]
  rw [balancedVariable_card_false hn]

private theorem v_fraction {n : ℕ} (hn : 4 ≤ n) :
    ((a n : ℝ) / v n) / ((a n : ℝ) / v n + 1) = alpha n := by
  have hv : (v n : ℝ) ≠ 0 := by exact_mod_cast (v_pos hn).ne'
  rw [alpha, div_add_one hv, div_div_div_cancel_right₀ hv]

private theorem u_fraction {n : ℕ} (hn : 4 ≤ n) :
    ((b n : ℝ) / u n) / ((b n : ℝ) / u n + 1) = beta n := by
  have hu : (u n : ℝ) ≠ 0 := by exact_mod_cast (u_pos hn).ne'
  rw [beta, div_add_one hu, div_div_div_cancel_right₀ hu]

/-- The complete actual second-trace estimate for the canonical parameters. -/
theorem configured_imm_second_moment_upper {n : ℕ} (hn : 16 ≤ n)
    (hbeta : beta n ≤ 2 / Real.sqrt (n : ℝ)) :
    let A := immNormalizedMatrix n (balancedLayer (show 4 ≤ n by omega)) (a n) (b n)
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      rankDimension n * rankMomentScale n ^ 2 * Real.exp (10 * Real.sqrt (n : ℝ)) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hn4 : 4 ≤ L + 1 := by omega
  let : Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) //
      balancedLayer hn4 x.1 = true} :=
    Fintype.card_pos_iff.mp (by rw [balancedVariable_card_true hn4]; exact v_pos hn4)
  let : Nonempty {x : Fin (L + 1) × (Fin (L + 1) × Fin (L + 1)) //
      ¬ balancedLayer hn4 x.1 = true} :=
    Fintype.card_pos_iff.mp (by
      simp only [Bool.not_eq_true]
      rw [balancedVariable_card_false hn4]
      exact u_pos hn4)
  have hraw := immNormalizedMatrix_second_moment_le_relaxed L
    (balancedLayer hn4) (a (L + 1)) (b (L + 1)) (a_pos hn4)
  dsimp only at hraw ⊢
  rw [configured_layerMeanV hn4, configured_layerMeanU hn4,
    v_fraction hn4, u_fraction hn4, card_immSourceIndex_eq_rankDimension hn4] at hraw
  apply configured_second_bound_of_path_bound hn hbeta _
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (sum_relaxed_pathWeight_balanced_le_exp hn (0 : Fin (L + 1)))
    (mul_nonneg (rankDimension_nonneg _) (sq_nonneg _)))

/-- A single eventual statement supplies the actual matrix premise required
by the final rank and circuit-size comparison. -/
theorem eventually_configured_imm_second_moment_upper :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ hn : 16 ≤ n,
      let A := immNormalizedMatrix n (balancedLayer (show 4 ≤ n by omega)) (a n) (b n)
      ((A.conjTranspose * A) ^ 2).trace.re ≤
        rankDimension n * rankMomentScale n ^ 2 * Real.exp (10 * Real.sqrt (n : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_second_moment_parameter_cutoff
  filter_upwards [Filter.eventually_ge_atTop N] with n hn hn16
  exact configured_imm_second_moment_upper hn16 (hN n hn).2.1

end Problem335.LowerParameters

end

end OAI
