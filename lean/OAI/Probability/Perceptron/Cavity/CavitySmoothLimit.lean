import Mathlib
import OAI.Probability.Perceptron.Variational.LevelTrialApprox
import OAI.Probability.Perceptron.Cavity.CavityTelescoping

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma expectedPressure_lower_smooth (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,(terminalVariational P α g.f).toReal-ε≤expectedPressure α 1 g.f (n+1) := by
  filter_upwards [cavity_averaged_log_lower P hB hα g h1 h2 h3 (show 0<ε/2 by positivity),
    bulkScale_per_coordinate_tendsto.eventually (Iio_mem_nhds (show 0<ε/2 by positivity))] with n hn he
  have hb:=cavityAveragedLog_unperturbed_bound hα.le g.f n
  linarith [(abs_le.mp hb).2]

theorem expectedPressure_limit_smooth (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) :
    Tendsto (fun n : ℕ=>expectedPressure α 1 g.f (n+1)) atTop
      (𝓝 (terminalVariational P α g.f).toReal) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [expectedPressure_lower_smooth P hB hα g h1 h2 h3 (show 0<ε/2 by positivity),
    expectedPressure_upper_variational P hB g ⟨α,hα.le⟩ (show 0<ε/2 by positivity)] with n hn hu
  change expectedPressure α 1 g.f (n+1) ≤ (terminalVariational P α g.f).toReal + ε/2 at hu
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩
end SphericalPerceptronFreeEnergy

end

end OAI
