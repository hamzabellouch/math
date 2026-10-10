import OAI.Combinatorics.KMedianRecovery.Refined.ConditionalRecovery
import OAI.Combinatorics.KMedian.Main

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

theorem companion_threshold_input : CompanionThresholdInput :=
  MetricKMedian.exists_internal_program

theorem refined_recovery :
    ∀ (bound : Polynomial ℕ) (ε L₀ : ℝ) (μ : ℚ),
      0 < ε → 0 < L₀ → 0 < μ → μ ≤ 1/4 → (μ : ℝ) ≤ ε/12 →
      ∃ A : BinaryRandomizedAlgorithm,
        PolynomialWork A bound ∧
        ∀ I : Input, I.Bounded bound → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
          (∀ s : Seed A I ζ, I.metric.Feasible (output A I ζ s)) ∧
          (∀ C : Certificate I μ L₀,
            1 - ζ ≤ successProbability A I ζ
              ((1 + 2 / Real.exp 1 + ε) * (I.metric.cost C.centers : ℝ))) :=
  refined_recovery_conditional companion_threshold_input

end MetricKMedianRecovery.RefinedRecovery

end OAI
