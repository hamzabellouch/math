import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Factors.ObservableWord
import OAI.Probability.FreeIsing.Gaussian.BernoulliSpectral
import OAI.Probability.FreeIsing.Ising.WalkObstruction

namespace OAI

noncomputable section

namespace Problem367

theorem IsFactorOfIID.threshold_of_centeredAverage_norm {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (hfactor : IsFactorOfIID d theta)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hnorm : ‖TreeKoopman.centeredAverage d‖ ≤ RadialWalk.rate d) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  obtain ⟨f, _, hcov⟩ := hfactor.exists_centered_word_observable hlo hhi
  apply IsingWalk.threshold_of_operatorAverage_norm hd hhi
    TreeKoopman.centeredGenerator TreeKoopman.centeredGenerator_sq f
  · simpa only [TreeKoopman.centered_operatorAverage_eq] using hnorm
  · exact hcov

theorem IsFactorOfIID.le_threshold {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (hfactor : IsFactorOfIID d theta)
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  apply hfactor.threshold_of_centeredAverage_norm hd hlo hhi
  exact TreeKoopman.centeredAverage_norm_le hd

theorem free_ising_factor_only_if_threshold (d : ℕ) (beta : ℝ)
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hfactor : IsFactorOfIID d (Real.tanh beta)) :
    Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  apply hfactor.le_threshold hd
  · exact le_trans (by norm_num) (tanh_nonneg_of_beta_nonneg hbeta)
  · exact (Real.tanh_lt_one beta).le

end Problem367

end

end OAI
