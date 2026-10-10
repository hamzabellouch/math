import Mathlib
import OAI.Probability.SphericalField.Quantiles.Convergence
import OAI.Probability.SphericalField.Quantiles.FiniteStationary
import OAI.Probability.SphericalField.Fields.DepthUniform

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

theorem boundedSphericalFieldValue_stationary_uniform (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q : BoundedField B,
      |boundedSphericalFieldValue (q.stationary hB1) n-
        ((entropy (quantileTrial (q.toQuantile hB1.le))).toReal-
          ∫ u, q.stationary hB1 u*q u ∂timeLaw)| < ε := by
  let H := B/(2*(1-B)^2)
  have hH : 0 ≤ H := div_nonneg hB0 (by positivity)
  filter_upwards [finiteSphericalFieldValue_all_depths_uniform H hH (ε/2) (half_pos hε)] with n hn q
  let qN : ℕ → BoundedField B := q.round
  have hq (u : Time) : Tendsto (fun N => qN N u) atTop (𝓝 (q u)) := q.round_tendsto u
  have hs (u : Time) : Tendsto (fun N => (qN N).stationary hB1 u) atTop (𝓝 (q.stationary hB1 u)) :=
    BoundedField.stationary_tendsto qN q hB1 hq u
  have hp := boundedSphericalFieldValue_tendsto_L1 (fun N => (qN N).stationary hB1) (q.stationary hB1)
    (BoundedField.L1_tendsto _ _ hs) n
  have he := entropy_quantileTrial_tendsto qN q hB1 hq
  have hc := BoundedField.integral_mul_tendsto (fun N => (qN N).stationary hB1) (q.stationary hB1) qN q hs hq
  have hh : ∀ N, |boundedSphericalFieldValue ((qN N).stationary hB1) n-
      ((entropy (quantileTrial ((qN N).toQuantile hB1.le))).toReal-
        ∫ u, (qN N).stationary hB1 u*qN N u ∂timeLaw)| ≤ ε/2 := by
    intro N
    let M := q.roundModel N
    let F := M.stationaryModel hB1
    have hm := hn F.depth F.weight F.value F.weight_pos F.weight_sum F.monotone_value
      (F.values_mem (ae_of_all _ fun u => ⟨((qN N).stationary hB1).nonneg u,((qN N).stationary hB1).le_bound u⟩) 0).1
      (F.values_mem (ae_of_all _ fun u => ⟨((qN N).stationary hB1).nonneg u,((qN N).stationary hB1).le_bound u⟩) (Fin.last F.depth)).2
    rw [boundedSphericalFieldValue_eq_finite ((qN N).stationary hB1) F n]
    change |finiteSphericalFieldValue n F.depth F.weight F.value-_| ≤ ε/2
    rw [M.stationary_minimum hB1] at hm
    exact hm.le
  exact (le_of_tendsto ((hp.sub (he.sub hc)).abs) (Eventually.of_forall hh)).trans_lt (half_lt_self hε)

end SphericalPerceptron
end
end

end OAI
