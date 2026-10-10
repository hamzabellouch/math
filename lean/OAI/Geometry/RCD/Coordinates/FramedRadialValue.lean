import OAI.Geometry.RCD.Coordinates.FramedRadialEnergy

namespace OAI

/-! # The Poisson radial value estimate in its normalizing frame -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

omit [IsFiniteMeasureOnCompacts μ] in
/-- The original coordinate covector has the gradient bound supplied by
its inverse normalizing frame. -/
theorem framed_directional_gradient {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (s : Set X) (L : ℝ)
    (hgrad : ∀ j, ∀ᵐ x ∂μ.restrict s,
      localGamma μ hQ (transformedColumn μ hQ u N j)
        (transformedColumn μ hQ u N j) x ≤ L ^ 2) (b : Euclidean n) :
    ∀ᵐ x ∂μ.restrict s,
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤
        ((n : ℝ) * L) ^ 2 * ‖N.symm b‖ ^ 2 := by
  have h := gamma_column_le_of_diagonal_bounds μ hQ (transformedColumn μ hQ u N)
    s L hgrad (N.symm b)
  simpa only [sobolevColumnMap_transformed, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h

/-- Transfer any actual distance fit to the same Poisson pairing. The
only new term is the already constructed Poisson energy error. -/
theorem DyadicDistanceReplacements.framed_value_transfer
    {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    {L : ℝ}
    (hgrad : ∀ j, ∀ᵐ x ∂μ.restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma μ hQ (transformedColumn μ hQ u N j)
        (transformedColumn μ hQ u N j) x ≤ L ^ 2)
    (b : Euclidean n)
    (G : LocalHessianPairing μ hQ (ball p (distanceSourceRadius r0 i / 64))
      (T.replacement i) (sobolevColumnMap μ hQ u b))
    (H : SobolevSpace μ hQ) {I Lbase : ℝ}
    (hbase : ∀ j, ∀ᵐ x ∂μ.restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma μ hQ (u j) (u j) x ≤ Lbase ^ 2)
    (hfit : ‖radialPairingLp μ hQ (ball p (distanceSourceRadius r0 i / 64))
        (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b)
        (gamma_column_le_of_diagonal_bounds μ hQ u _ Lbase hbase b) -
      SobolevSpace.restrictLp μ hQ (ball p (distanceSourceRadius r0 i / 64)) H‖ ^ 2 ≤ I) :
    ‖SobolevSpace.restrictLp μ hQ (ball p (distanceSourceRadius r0 i / 64)) (G.mixed - H)‖ ^ 2 ≤
      2 * I + 2 * (((n : ℝ) * L) ^ 2 * ‖N.symm b‖ ^ 2) *
        ((S.source i).real (ball p (distanceSourceRadius r0 i)) *
          (B * (distanceSourceRadius r0 i) ^ 2)) := by
  have ha := framed_directional_gradient μ hQ u N _ L hgrad b
  apply G.fit_value_transfer μ hQ (T.distanceDatum μ hQ i) H
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ha (T.local_energy_error μ hQ i _)
  have he := radialPairingLp_congr μ hQ _ (T.distanceDatum μ hQ i)
    (sobolevColumnMap μ hQ u b) (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b)
    ha (gamma_column_le_of_diagonal_bounds μ hQ u _ Lbase hbase b)
    (Filter.EventuallyEq.rfl)
  rw [he]
  exact hfit

end RegularPointCoordinates

end

end OAI
