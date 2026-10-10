import OAI.Geometry.RCD.Heat.GaussianMomentIntegrable
import OAI.Geometry.RCD.Harmonic.ContinuousRadialMoment

namespace OAI

/-! # Integrability of a Gaussian under exponential volume growth -/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem gaussian_integrable (p : X) {V B c : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (hc : 0 < c)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R)) :
    Integrable (fun x => Real.exp (-c*(dist x p)^2)) μ := by
  have hg : Integrable (fun x => Real.exp (-c*(dist x p)^2)*(dist x p)^2) μ := by
    simpa only [dist_comm] using gaussian_second_moment_integrable μ p hV hB hc hvol
  have hw := integrable_one_add_sq_of_tail
    (show Continuous (fun x => Real.exp (-c*(dist x p)^2)) by fun_prop)
    (fun x => (Real.exp_pos _).le) p (by norm_num : (0:ℝ) < 1)
    hg.integrableOn
  apply hw.mono'
  · fun_prop
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have hh := mul_nonneg (Real.exp_pos (-c*(dist x p)^2)).le (sq_nonneg (dist x p))
    nlinarith

end RegularPointCoordinates

end

end OAI
