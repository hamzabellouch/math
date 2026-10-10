import OAI.Geometry.RCD.Coordinates.DyadicRadialFits

namespace OAI

/-! # The canonical actual dyadic radial-fit sequence -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [IsFiniteMeasureOnCompacts (hausdorff n X)]

/-- The bound only supplies local L2 membership. The numerical value is
the actual least-squares residual for the canonical distance derivative. -/
def dyadicRadialFit {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ)
    (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (i : ℕ) (b : Euclidean n) : ℝ :=
  radialFitError (hausdorff n X) hX.quadratic u p (distanceSourceRadius r0 i / 64)
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (T.distanceDatum (hausdorff n X) hX.quadratic i)
    (sobolevColumnMap (hausdorff n X) hX.quadratic u b)
    (gamma_column_le_of_diagonal_bounds (hausdorff n X) hX.quadratic u _ L (hbase i) b)

theorem dyadicRadialFit_nonneg {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
    (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ)
    (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
    (i : ℕ) (b : Euclidean n) : 0 ≤ dyadicRadialFit hX T u L hbase i b := by
  apply radialFitError_nonneg
  exact (div_pos (distanceSourceRadius_pos S.radius_pos i) (by norm_num)).le

end RegularPointCoordinates

end

end OAI
