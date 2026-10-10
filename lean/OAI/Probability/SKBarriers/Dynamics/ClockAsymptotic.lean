import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageScale

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem stretched_attempt_error_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-((n:ℝ)^kappa))) atTop (𝓝 0) := by
  have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/kappa) 1 zero_lt_one).comp
    stretchedLogScale_tendsto
  apply H.congr'
  filter_upwards with n
  change ((n:ℝ)^kappa)^(1/kappa)*Real.exp (-1*((n:ℝ)^kappa)) = _
  rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ n),show kappa*(1/kappa)=1 by norm_num [kappa],
    Real.rpow_one,neg_one_mul]

theorem eventually_attempt_error_small :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)*Real.exp (-((n:ℝ)^kappa)) ≤ (1/8:ℝ) :=
  (stretched_attempt_error_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8))).mono
    (fun _ h => le_of_lt h)

end SK.Analytic

end
end

end

end OAI
