import Mathlib
import OAI.Analysis.BiholderTransport.Model

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport
open Matrix
open scoped MatrixOrder
open scoped BoundedContinuousFunction

section DensityBounds
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
omit [MetricSpace M] [BorelSpace M] [CompactSpace M] in

lemma densityMeasure_bounds {vol : Measure M} {lam cap : ℝ} {rho : M → ℝ}
    (hrho : AdmissibleDensity vol lam cap rho) :
    ENNReal.ofReal lam • vol ≤ densityMeasure vol rho ∧
      densityMeasure vol rho ≤ ENNReal.ofReal cap • vol := by
  constructor
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hrho.2.2.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.1
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [hrho.2.2.2] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2

omit [MetricSpace M] [BorelSpace M] [CompactSpace M] in
lemma volume_absolutelyContinuous_densityMeasure {vol : Measure M} {lam cap : ℝ}
    {rho : M → ℝ} (hlam : 0 < lam) (hrho : AdmissibleDensity vol lam cap rho) :
    vol ≪ densityMeasure vol rho := by
  apply withDensity_absolutelyContinuous' hrho.1.ennreal_ofReal
  filter_upwards [hrho.2.2.2] with x hx
  exact (ENNReal.ofReal_pos.mpr (hlam.trans_le hx.1)).ne'
end DensityBounds

end WeakMTWTransport
end
end
end

end OAI
