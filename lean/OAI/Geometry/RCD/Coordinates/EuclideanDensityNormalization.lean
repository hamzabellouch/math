import OAI.Geometry.RCD.Coordinates.NormalizedDensityLaw
import OAI.Geometry.RCD.Metric.MeasuredBallLaw

namespace OAI

/-! # Interior Euclidean densities have the same normalized law at either scale -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_density_inside {n : ℕ} {S : ℝ} (hS : 0<S)
    (a : Euclidean n →ᵇ ℝ) (ha : ∀ x, 0≤a x) (hi : Integrable a volume)
    (hzero : ∀ x, x∉ball (0:Euclidean n) S → a x=0)
    (hp : 0<∫ x, a x) (hpb : 0<∫ x, a x ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
      (a.integrable _) ha hpb=normalizedDensityLaw volume hi ha hp := by
  have hV : 0<volume.real (ball (0:Euclidean n) S) := ENNReal.toReal_pos
    (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top
  have hm : (∫ x, a x ∂(euclideanBallProbability n S : Measure (Euclidean n)))=
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ x, a x) := by
    rw [euclideanBallProbability_integral hS, setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding _).injective
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro φ
  change (∫ x, φ x ∂(normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
    (a.integrable _) ha hpb : Measure (Euclidean n)))=
    ∫ x, φ x ∂(normalizedDensityLaw volume hi ha hp : Measure (Euclidean n))
  rw [normalizedDensityLaw_integral _ a.continuous.measurable,
    normalizedDensityLaw_integral _ a.continuous.measurable,hm,
    euclideanBallProbability_integral hS]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx,zero_mul])]
  field_simp [hV.ne',hp.ne']

end RegularPointCoordinates

end

end OAI
