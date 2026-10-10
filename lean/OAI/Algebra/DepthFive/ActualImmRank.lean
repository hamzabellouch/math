import OAI.Algebra.DepthFive.ConfiguredRankData
import OAI.Algebra.DepthFive.ImmFiniteMatrix
import OAI.Algebra.DepthFive.BidegreeDimension
import OAI.Algebra.DepthFive.ImmFirstMomentParameters

namespace OAI

/-! Identification of the concrete rank measure with the finite normalized
matrix used in the IMM trace estimates. -/

noncomputable section

namespace Problem335.LowerParameters

theorem card_immSourceIndex_eq_rankDimension {n : ℕ} (hn : 4 ≤ n) :
    (Fintype.card (ImmSourceIndex n (balancedLayer hn) (a n) (b n)) : ℝ) =
      rankDimension n := by
  have h := card_bidegree_finsupp_exponents
    (fun x : Fin n × Fin n × Fin n => balancedLayer hn x.1) (a n) (b n)
  rw [balancedVariable_card_true hn, balancedVariable_card_false hn,
    Nat.multichoose_eq, Nat.multichoose_eq] at h
  simp only [Nat.card_eq_fintype_card] at h
  unfold rankDimension homogeneousDim
  exact_mod_cast h

theorem rankData_imm_eq_matrixRank {n : ℕ} (hn : 4 ≤ n) :
    rankData n (imm ℂ n) =
      ((immNormalizedMatrix n (balancedLayer hn) (a n) (b n)).rank : ℝ) := by
  rw [rankData_eq hn, immNormalizedMatrix_rank]
  simp only [immLayerVCount, immLayerUCount,
    balancedLayer_card_true hn, balancedLayer_card_false hn]

/-- The configured actual first trace, in the common normalization used by
the final rank comparison. -/
theorem configured_imm_first_trace_lower {n : ℕ} (hn : 16 ≤ n) :
    rankDimension n * rankMomentScale n * Real.exp (-(64 * Real.sqrt (n : ℝ))) ≤
      ((immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)).conjTranspose *
        immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)).trace.re := by
  have hn4 : 4 ≤ n := by omega
  have h := immNormalizedMatrix_first_moment_lower_sqrt hn (balancedLayer hn4)
    (balancedLayer_card_true hn4) (balancedLayer_card_false hn4)
  rw [card_immSourceIndex_eq_rankDimension hn4] at h
  simpa only [rankMomentScale, mul_assoc, neg_mul] using h

/-- After the actual first-moment estimate is discharged, the sole remaining
matrix hypothesis for the configured rank lower bound is the second trace. -/
theorem rankData_imm_lower_of_second_trace_bound {n : ℕ} (hn : 16 ≤ n) (C : ℝ)
    (hsecond :
      (((immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)).conjTranspose *
        immNormalizedMatrix n (balancedLayer (Nat.le_trans (of_decide_eq_true rfl : 4 ≤ 16) hn)) (a n) (b n)) ^ 2).trace.re ≤
        rankDimension n * rankMomentScale n ^ 2 * Real.exp (C * Real.sqrt (n : ℝ))) :
    rankDimension n * Real.exp (-((128 + C) * Real.sqrt (n : ℝ))) ≤
      rankData n (imm ℂ n) := by
  have hn4 : 4 ≤ n := by omega
  have h := rank_lower_bound_of_trace_moment_bounds
    (immNormalizedMatrix n (balancedLayer hn4) (a n) (b n))
    (rankDimension_pos hn4) (rankMomentScale_pos hn4)
    (configured_imm_first_trace_lower hn) hsecond
  rw [← rankData_imm_eq_matrixRank hn4] at h
  have he : 2 * (64 * Real.sqrt (n : ℝ)) + C * Real.sqrt (n : ℝ) =
      (128 + C) * Real.sqrt (n : ℝ) := by ring
  simpa only [he] using h

end Problem335.LowerParameters

end

end OAI
