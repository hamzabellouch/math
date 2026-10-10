import OAI.Geometry.RCD.Heat.GaussianMomentEnvelope
import OAI.Analysis.RCDHeat.WeightedHilbert

namespace OAI

/-! # Gaussian moments on a space with exponential volume growth -/

open Set Filter MeasureTheory Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem gaussian_second_moment_integrable (p : X) {V B c : ℝ}
    (hV : 0 ≤ V) (hB : 0 ≤ B) (hc : 0 < c)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (closedBall p (2*R)) ≤ V*Real.exp (B*R)) :
    Integrable (fun x => Real.exp (-c*(dist p x)^2)*(dist p x)^2) μ := by
  have ha : 0 ≤ B+1 := by linarith
  obtain ⟨C,hC,hbound⟩ := gaussian_moment_exponential_bound ha hc
  have hi := (integrable_exp_neg_dist_of_volume μ p hV hB (by linarith : B < B+1) hvol).const_mul C
  apply hi.mono'
  · fun_prop
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hbound (dist p x) dist_nonneg

end RegularPointCoordinates

end

end OAI
