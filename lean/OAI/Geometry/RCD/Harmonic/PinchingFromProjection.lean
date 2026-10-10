import OAI.Geometry.RCD.Sobolev.MeanGradient
import OAI.Geometry.RCD.Sobolev.ScalarAbsorption

namespace OAI

/-!
# From a sharp projection to directional mass

The residual energy, constant-direction estimate and mass estimates are
kept explicit. The coefficient-recovery step uses the actual normalized
Sobolev Gram. The local Bochner estimates supplying the other hypotheses
are not asserted here.
-/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  (U : E →L[ℝ] SobolevSpace μ hQ) (s : Set X) (hs : MeasurableSet s)

/-- The constant-direction error and the sharp projection energy control
the difference between the true coordinate displacement and the fitted
linear coefficient. All errors remain squared. -/
theorem coefficient_recovery_sq
    (hnormal : sobolevMeanGram μ hQ U s hs = ContinuousLinearMap.id ℝ E)
    (f : SobolevSpace μ hQ) (b δ : E) {e d : ℝ}
    (henergy : (μ.real s)⁻¹ * ∫ x in s,
      (SobolevSpace.minimalSlope μ hQ (f - U b) x) ^ 2 ∂μ ≤ e)
    (hdirection : ‖meanGradientVector μ hQ U s hs f - δ‖ ^ 2 ≤ d) :
    ‖δ - b‖ ^ 2 ≤ 2 * (d + e) := by
  have hb := (meanGradientVector_coefficient_error μ hQ U s hs hnormal f b).trans henergy
  have hid : δ - b = -(meanGradientVector μ hQ U s hs f - δ) +
      (meanGradientVector μ hQ U s hs f - b) := by abel
  have hnorm := norm_add_le (-(meanGradientVector μ hQ U s hs f - δ))
    (meanGradientVector μ hQ U s hs f - b)
  rw [← hid, norm_neg] at hnorm
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hnorm
  nlinarith [sq_nonneg (‖meanGradientVector μ hQ U s hs f - δ‖ -
    ‖meanGradientVector μ hQ U s hs f - b‖)]

/-- Transfer small mass from the fitted coefficient to the actual
coordinate displacement. This also allows a singular local mass form. -/
theorem directional_mass_of_projection
    (hnormal : sobolevMeanGram μ hQ U s hs = ContinuousLinearMap.id ℝ E)
    (f : SobolevSpace μ hQ) (b δ : E) (D : E →L[ℝ] E)
    (hD : D.IsPositive) {e d m K : ℝ} (hK : 0 ≤ K)
    (henergy : (μ.real s)⁻¹ * ∫ x in s,
      (SobolevSpace.minimalSlope μ hQ (f - U b) x) ^ 2 ∂μ ≤ e)
    (hdirection : ‖meanGradientVector μ hQ U s hs f - δ‖ ^ 2 ≤ d)
    (hmass : ⟪b, D b⟫_ℝ ≤ m)
    (hupper : ∀ v, ⟪v, D v⟫_ℝ ≤ K * ‖v‖ ^ 2) :
    ⟪δ, D δ⟫_ℝ ≤ 2 * m + 4 * K * (d + e) := by
  have hcoeff := coefficient_recovery_sq μ hQ U s hs hnormal f b δ henergy hdirection
  have herr := (hupper (δ - b)).trans (mul_le_mul_of_nonneg_left hcoeff hK)
  let v := δ - b
  have hp := hD.inner_nonneg_right (b - v)
  have hsym : ⟪v, D b⟫_ℝ = ⟪b, D v⟫_ℝ := by
    rw [real_inner_comm, hD.inner_left_eq_inner_right]
  have hid : δ = b + v := by dsimp [v]; abel
  have he : ⟪δ, D δ⟫_ℝ = ⟪b, D b⟫_ℝ +
      2 * ⟪b, D v⟫_ℝ + ⟪v, D v⟫_ℝ := by
    conv_lhs => rw [hid]
    simp only [map_add, inner_add_left, inner_add_right, hsym]
    ring
  simp only [map_sub, inner_sub_left, inner_sub_right, hsym] at hp
  change ⟪v, D v⟫_ℝ ≤ K * (2 * (d + e)) at herr
  nlinarith

end RegularPointCoordinates

end

end OAI
