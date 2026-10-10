import OAI.Geometry.RCD.Coordinates.DyadicRadialFit

namespace OAI

/-! # Compatible local L2 targets for consecutive actual affine fits -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [IsFiniteMeasureOnCompacts (hausdorff n X)]
  {κ r0 B J C L : ℝ} {p : X}
  {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
  (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
  (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
  (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 64)),
    localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ L ^ 2)

def dyadicRadialTarget (i : ℕ) (b : Euclidean n) :
    Lp ℝ 2 ((hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 64))) :=
  radialPairingLp (hausdorff n X) hX.quadratic (ball p (distanceSourceRadius r0 i / 64))
    (T.distanceDatum (hausdorff n X) hX.quadratic i)
    (sobolevColumnMap (hausdorff n X) hX.quadratic u b)
    (gamma_column_le_of_diagonal_bounds (hausdorff n X) hX.quadratic u _ L (hbase i) b)

theorem dyadicRadialTarget_residual_norm (i : ℕ) (b : Euclidean n) :
    ‖normalizeLocalL2 (hausdorff n X) (ball p (distanceSourceRadius r0 i / 64))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (affineResidual (hausdorff n X) hX.quadratic u (ball p (distanceSourceRadius r0 i / 64))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (dyadicRadialTarget hX T u hbase i b))‖ =
      (distanceSourceRadius r0 i / 64) * dyadicRadialFit hX T u L hbase i b := by
  unfold dyadicRadialTarget dyadicRadialFit radialFitError
  field_simp [(distanceSourceRadius_pos S.radius_pos i).ne']

/-- Although the compact distance primitives change with scale, their
actual radial derivatives agree under restriction. -/
theorem dyadicRadialTarget_restrict {i j : ℕ} (hij : i ≤ j) (b : Euclidean n) :
    let hsub := ball_subset_ball (div_le_div_of_nonneg_right
      (distanceSourceRadius_antitone S.radius_pos.le hij) (by norm_num : (0 : ℝ) ≤ 64))
    localL2Restriction (hausdorff n X) (ball p (distanceSourceRadius r0 i / 64))
      (ball p (distanceSourceRadius r0 j / 64)) hsub (dyadicRadialTarget hX T u hbase i b) =
        dyadicRadialTarget hX T u hbase j b := by
  dsimp only
  let μ := hausdorff n X
  let a := sobolevColumnMap μ hX.quadratic u b
  have hsub : ball p (distanceSourceRadius r0 j / 64) ⊆ ball p (distanceSourceRadius r0 i / 64) :=
    ball_subset_ball (div_le_div_of_nonneg_right
      (distanceSourceRadius_antitone S.radius_pos.le hij) (by norm_num))
  have hi := gamma_column_le_of_diagonal_bounds μ hX.quadratic u _ L (hbase i) b
  have hj := gamma_column_le_of_diagonal_bounds μ hX.quadratic u _ L (hbase j) b
  have hit := ae_restrict_of_ae_restrict_of_subset hsub hi
  change localL2Restriction μ _ _ hsub (radialPairingLp μ hX.quadratic _ _ a hi) =
    radialPairingLp μ hX.quadratic _ _ a hj
  rw [radialPairingLp_restrict μ hX.quadratic hsub _ a hi hit]
  exact radialPairingLp_congr μ hX.quadratic _ _ a _ a hit hj
    (T.distanceDatum_pairing_later μ hX.quadratic hij a)

end RegularPointCoordinates

end

end OAI
