import OAI.Geometry.RCD.Coordinates.DyadicRadialFits
import OAI.Geometry.RCD.Harmonic.RadialPairingSize

namespace OAI

/-! # The actual distance derivative has radius times covector size -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem DyadicDistanceReplacements.distanceDatum_energy_bound
    {n : ℕ} {κ r0 B J C : ℝ} {p : X} {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hrr : r ≤ 4 * distanceSourceRadius r0 i) :
    ∀ᵐ x ∂μ.restrict (ball p r),
      localGamma μ hQ (T.distanceDatum μ hQ i) (T.distanceDatum μ hQ i) x ≤ r ^ 2 := by
  let s := distanceSourceRadius r0 i
  have hs : 0 ≤ 4 * s := by have := distanceSourceRadius_pos S.radius_pos i; positivity
  have hsub : ball p r ⊆ ball p (4 * s) := ball_subset_ball hrr
  have he := positiveSquaredDistance_energy_value μ hQ hs (T.cutoff i) (S.eikonal i)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub he,
    ae_restrict_of_ae (positiveSquaredDistance_representative μ hQ hs (T.cutoff i)),
    ae_restrict_mem measurableSet_ball] with x he hx hxr
  have hv := positiveSquaredDistanceValue_on_ball μ hQ (T.cutoff i) (hsub hxr)
  have hd : dist p x ≤ r := by
    have hx' : dist x p < r := hxr
    simpa only [dist_comm] using hx'.le
  have hsq : dist p x ^ 2 ≤ r ^ 2 := (sq_le_sq₀ dist_nonneg hr).mpr hd
  change (1 / 2 : ℝ) * localGamma μ hQ (T.distanceDatum μ hQ i)
    (T.distanceDatum μ hQ i) x = SobolevSpace.toLp μ hQ (T.distanceDatum μ hQ i) x at he
  have hv' : SobolevSpace.toLp μ hQ (T.distanceDatum μ hQ i) x = dist p x ^ 2 / 2 := hx.trans hv
  rw [hv'] at he
  linarith

/-- The raw radial target of every original covector is bounded in the
current normalizing frame. This supplies the vanishing affine-center bound. -/
theorem DyadicDistanceReplacements.radialPairing_size
    {n : ℕ} {κ r0 B J C ε : ℝ} {p : X} {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hrr : r ≤ 4 * distanceSourceRadius r0 i)
    (hfin : μ (ball p r) ≠ ∞) (hzero : μ (ball p r) ≠ 0) (hε : 0 ≤ ε)
    (u : Fin n → SobolevSpace μ hQ) (F : Euclidean n ≃L[ℝ] Euclidean n)
    (hgrad : ∀ j, ∀ᵐ x ∂μ.restrict (ball p r),
      localGamma μ hQ (transformedColumn μ hQ u F j) (transformedColumn μ hQ u F j) x ≤ (1 + ε) ^ 2)
    (b : Euclidean n) {H : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (ball p r),
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤ H) :
    ‖normalizeLocalL2 μ (ball p r) hfin
      (radialPairingLp μ hQ (ball p r) (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) ha)‖ ≤
      r * ((n : ℝ) * (1 + ε)) * ‖F.symm b‖ := by
  have hbound := gamma_column_le_of_diagonal_bounds μ hQ (transformedColumn μ hQ u F)
    (ball p r) (1 + ε) hgrad (F.symm b)
  rw [sobolevColumnMap_transformed] at hbound
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at hbound
  have he := radialPairingLp_congr μ hQ (ball p r) (T.distanceDatum μ hQ i)
    (sobolevColumnMap μ hQ u b) (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b)
    ha hbound (Filter.Eventually.of_forall fun _ => rfl)
  rw [he]
  have hsize := normalized_gamma_size μ hQ (ball p r) hfin hzero
    (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) (sq_nonneg r) (by positivity)
    (T.distanceDatum_energy_bound μ hQ i hr hrr) hbound
  apply hsize.trans_eq
  rw [show r ^ 2 * (((n : ℝ) * (1 + ε)) ^ 2 * ‖F.symm b‖ ^ 2) =
    (r * ((n : ℝ) * (1 + ε)) * ‖F.symm b‖) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

end RegularPointCoordinates

end

end OAI
