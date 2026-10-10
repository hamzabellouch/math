import OAI.Geometry.RCD.Sobolev.BoundedEnergyDensity
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Differentiation

namespace OAI

/-! # Almost-everywhere density of the actual finite Euclidean energy measure -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_energy_density_limit {n : ℕ} (ν : FiniteMeasure (Euclidean n)) :
    ∀ᵐ x ∂(volume : Measure (Euclidean n)),
      Tendsto (fun r => (ν : Measure (Euclidean n)).real (closedBall x r)/
        volume.real (closedBall x r)) (𝓝[>] 0)
        (𝓝 (((ν : Measure (Euclidean n)).rnDeriv volume x).toReal)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν : Measure (Euclidean n)) volume,
    Measure.rnDeriv_ne_top (ν : Measure (Euclidean n)) volume] with x hx hfinite
  have hh := (ENNReal.tendsto_toReal hfinite).comp hx
  simpa only [Function.comp_def,ENNReal.toReal_div,Measure.real] using hh

end RegularPointCoordinates

end

end OAI
