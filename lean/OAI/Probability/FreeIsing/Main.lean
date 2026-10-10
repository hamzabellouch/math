import OAI.Probability.FreeIsing.Ising.ActualVarianceAnalysis
import OAI.Probability.FreeIsing.Ising.SharpVarianceRecovery
import OAI.Probability.FreeIsing.Support

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem free_ising_factor_below_threshold :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta → Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) → IsFactorOfIID d (Real.tanh beta) := by
  apply free_ising_factor_below_threshold_of_actual_variance_identity
  intro d beta hd hb hcrit T
  exact IsingObservationFactor.actual_variance_analysis hd
    (freeIsingMeasure_hasFreeIsingLaw d (Real.neg_one_lt_tanh beta).le
      (Real.tanh_lt_one beta).le) hb.le hcrit T

theorem free_ising_factor_iff_threshold :
    ∀ (d : ℕ) (beta : ℝ), 3 ≤ d → 0 ≤ beta → (IsFactorOfIID d (Real.tanh beta) ↔ Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) := by
  intro d beta hd hbeta
  exact ⟨free_ising_factor_only_if_threshold d beta hd hbeta,
    free_ising_factor_below_threshold d beta hd hbeta⟩

end Problem367

end

end OAI
