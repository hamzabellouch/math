import OAI.Geometry.RCD.Sobolev.ContinuousLocalGradientBound
import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives

namespace OAI

/-! # Pointwise oscillation of the actual coordinate directions -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem NoncollapsedRCD.column_value_bound_of_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (p : X) {R : ℝ} (hR : 0 < R)
    (hv : ContinuousOn v (ball p (8*R)))
    (hrep : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i) =ᵐ[
      (hausdorff n X).restrict (ball p (8*R))] fun x => v x i)
    (z : Euclidean n) (L : ℝ≥0)
    (hgrad : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*R)),
      localGamma (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u z)
        (sobolevColumnMap (hausdorff n X) hX.quadratic u z) x ≤ (L : ℝ)^2) :
    ∀ x ∈ ball p R, |⟪v x-v p,z⟫_ℝ| ≤ (L : ℝ)*dist x p := by
  have hb := hX.continuous_local_gradient_bound hn
    (sobolevColumnMap (hausdorff n X) hX.quadratic u z) (fun x => ⟪v x,z⟫_ℝ) p hR L
    (hv.inner continuousOn_const)
    (sobolevColumnMap_representative (hausdorff n X) hX.quadratic u (ball p (8*R)) v hrep z) hgrad
  simpa only [inner_sub_left] using hb

end RegularPointCoordinates

end

end OAI
