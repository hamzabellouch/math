import OAI.Geometry.RCD.Metric.NearMaximalDistanceSources
import OAI.Geometry.RCD.Coordinates.RegularMovingVolume

namespace OAI

/-! # Vanishing actual distance sources near a regular point

The absolute volume limits are constructed from regularity, rather than
assumed for the selected centers and radii.
-/

open Set Filter Metric MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_moving_distance_sources {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (hK : K≤0)
    {o : X} (ho : IsRegular n o)
    (p : ℕ → X) (r : ℕ → ℝ) (hp : Tendsto p atTop (𝓝 o))
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    ∃ σ : ℕ → Measure X,
      (∀ k, IsFiniteMeasure (σ k)) ∧
      (∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (4*r k)),
        localGamma (hausdorff n X) hX.quadratic
          (inwardSobolev (hausdorff n X) hX.quadratic (p k) (4*r k))
          (inwardSobolev (hausdorff n X) hX.quadratic (p k) (4*r k)) x=1) ∧
      (∀ k (C : ℝ) (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic (p k) (4*r k) C)
        (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (L : ℝ≥0),
        LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball (p k) (r k) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        energyForm (hausdorff n X) hX.quadratic
          (positiveSquaredDistance (hausdorff n X) hX.quadratic
            (mul_nonneg (by norm_num) (hr k).le) χ) ψ+
          ((n:ℝ)+(-K)*(4*r k)^2)*(∫ x in ball (p k) (r k), v x ∂hausdorff n X)=∫ x, v x ∂σ k) ∧
      Tendsto (fun k => (r k)^(-(n:ℝ))*(σ k).real (ball (p k) (r k))) atTop (𝓝 0) := by
  have hv (s : ℕ → ℝ) (hs : ∀ k, 0<s k) (hs0 : Tendsto s atTop (𝓝 0)) :
      Tendsto (fun k => (s k)^(-(n:ℝ))*(hausdorff n X).real (ball (p k) (s k)))
        atTop (𝓝 (euclideanUnitVolume n)) := by
    convert hX.regular_moving_volume_limit hn ho p s hp hs hs0 using 1
    funext k
    rw [Real.rpow_neg (hs k).le,Real.rpow_natCast,div_eq_inv_mul]
  have ht : Tendsto (fun k => 2*r k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hr0.const_mul 2
  exact hX.distance_sources_from_volume_limits hn hK p r hr hr0 (hv r hr hr0)
    (hv (fun k => 2*r k) (fun k => mul_pos (by norm_num) (hr k)) ht)

end RegularPointCoordinates

end

end OAI
