import OAI.Geometry.RCD.Metric.ImageMassErrorLimit
import OAI.Geometry.RCD.Metric.ActualImageMassDensity

namespace OAI

/-! # Absolute regular-point volume convergence from actual coordinate images -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_volume_convergence_nonpositive {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hK : K≤0) {p : X} (hp : IsRegular n p) :
    EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  obtain ⟨θ,_hθ,hθupper,hdensity⟩ := hX.rescaling_volume_density hn p
  have hlower : euclideanUnitVolume n ≤ θ := by
    apply unit_volume_le_density_of_image_bounds n (euclideanUnitVolume n) θ
      (imageMassErrorConstant n) ((Real.cosh 1^(n-1)*2^n)*(16*16384)^n) (by positivity)
    intro η hη hηsmall ζ hζ hζsmall
    exact hX.actual_image_mass_density_bound hn hK hp hdensity hη hηsmall hζ hζsmall
  have hθeq : θ=euclideanUnitVolume n := le_antisymm hθupper hlower
  apply rescaling_volume_convergence_of_density
  intro s hs hs0
  simpa only [hθeq,mul_one,one_pow] using hdensity s hs hs0 1 zero_lt_one

end RegularPointCoordinates

end

end OAI
