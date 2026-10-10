import OAI.Geometry.RCD.Coordinates.FramedRadialSmallness
import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # The qualitative estimate at the actual normalization radius -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

def radialNormalizationRestrictionConstant (n : ℕ) : ℝ := (5 / 3 : ℝ) * (32 : ℝ) ^ n

theorem radialNormalizationRestrictionConstant_ge_one (n : ℕ) :
    1 ≤ radialNormalizationRestrictionConstant n := by
  have hh : (1 : ℝ) ≤ 32 ^ n := one_le_pow₀ (by norm_num)
  dsimp only [radialNormalizationRestrictionConstant]
  linarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The normalizing ball has radius twice the distance-source radius.
Its first-order and metric estimates control the original radial fit on
the testing ball with an explicit, scale-independent coefficient. -/
theorem DyadicDistanceReplacements.normalized_frame_fit_smallness
    {n : ℕ} {κ r0 B J C omega δ Cχ : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (homega : 0 < omega) (hδ : 0 ≤ δ)
    (hδ1 : radialNormalizationRestrictionConstant n * δ ≤ 1) (hCχ : 0 ≤ Cχ)
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ 2 * distanceSourceRadius r0 i →
      |μ.real (ball p t) / (omega * t ^ n) - 1| ≤ 1 / 4)
    (u : Fin n → SobolevSpace μ hQ) (A : Euclidean n ≃L[ℝ] Euclidean n)
    (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (2 * distanceSourceRadius r0 i) δ
      (transformedColumn μ hQ u A) v)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v x - v p)))
    (χ : GoodLaplacianCutoff μ hQ p (distanceSourceRadius r0 i / 64) Cχ)
    (b : Euclidean n) {L : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤ L) :
    let r := distanceSourceRadius r0 i / 64
    let hfin : μ (ball p r) ≠ ∞ := ne_of_lt
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p r).measure_lt_top)
    (radialFitError μ hQ u p r hfin (T.distanceDatum μ hQ i) (sobolevColumnMap μ hQ u b) ha) ^ 2 ≤
      ((n : ℝ) * (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1))) *
        radialNormalizationRestrictionConstant n * ((5 / 3 : ℝ) * (4 : ℝ) ^ n) * δ * ‖A.symm b‖ ^ 2 := by
  dsimp only
  let s := distanceSourceRadius r0 i
  let r := s / 64
  let D := radialNormalizationRestrictionConstant n
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hr : 0 < r := by dsimp only [r]; positivity
  have hD : 1 ≤ D := radialNormalizationRestrictionConstant_ge_one n
  have hε : 0 ≤ D * δ := mul_nonneg (zero_le_one.trans hD) hδ
  have hv (t : ℝ) (ht : 0 < t) (hts : t ≤ 2 * s) :
      0 < μ.real (ball p t) := (quarter_volume_bounds ht homega (hquarter t ht hts)).1
  have hfin (t : ℝ) : μ (ball p t) ≠ ∞ := ne_of_lt
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p t).measure_lt_top)
  have hzero (t : ℝ) (ht : 0 < t) (hts : t ≤ 2 * s) : μ (ball p t) ≠ 0 := by
    intro hz
    have hp := hv t ht hts
    rw [Measure.real, hz, ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp
  have hratio : μ.real (ball p (2 * s)) / μ.real (ball p (4 * r)) ≤ D := by
    have h := radial_fraction_volume_ratio (show 0 < 2 * s by positivity)
      (by norm_num : (0 : ℝ) < 1 / 32) homega
      (hquarter (2 * s) (by positivity) le_rfl)
      (hquarter ((1 / 32 : ℝ) * (2 * s)) (by positivity) (by linarith))
    have hrad : (1 / 32 : ℝ) * (2 * s) = 4 * r := by dsimp only [r]; ring
    rw [hrad] at h
    have hp : (((1 / 32 : ℝ) ^ n)⁻¹) = (32 : ℝ) ^ n := by rw [← inv_pow]; norm_num
    simpa only [D, radialNormalizationRestrictionConstant, hp] using h
  have hsub : ball p (4 * r) ⊆ ball p (2 * s) := ball_subset_ball (by dsimp only [r]; linarith)
  have hlocal := hfirst.restrict_ball μ hQ hsub hδ hD
    (hzero (4 * r) (by positivity) (by dsimp only [r]; linarith)) (hfin _)
    (hzero (2 * s) (by positivity) le_rfl) (hfin _)
    ((div_le_iff₀ (hv (4 * r) (by positivity) (by dsimp only [r]; linarith))).mp hratio)
  have hη : SobolevSpace.toLp μ hQ (T.cutoff i).sobolev =ᵐ[μ.restrict (ball p (4 * r))]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (T.cutoff i).representative,
      ae_restrict_mem measurableSet_ball] with x hx hxr
    exact hx.trans ((T.cutoff i).one x
      ((ball_subset_ball (show 4 * r ≤ 4 * s by dsimp only [r]; linarith)) hxr))
  have hmetric' := hmetric.mono_error (show δ ≤ D * δ by nlinarith)
  have hsmall := T.framed_covector_fit_smallness μ hQ i hε hδ1 hCχ u A v
    hlocal hmetric' (T.cutoff i).sobolev hη χ
    (hv (4 * r) (by positivity) (by dsimp only [r]; linarith)) b ha
  dsimp only at hsmall
  have hratio4 : μ.real (ball p (4 * r)) / μ.real (ball p r) ≤ (5 / 3 : ℝ) * (4 : ℝ) ^ n := by
    have h := radial_fraction_volume_ratio (show 0 < 4 * r by positivity)
      (by norm_num : (0 : ℝ) < 1 / 4) homega
      (hquarter (4 * r) (by positivity) (by dsimp only [r]; linarith))
      (hquarter ((1 / 4 : ℝ) * (4 * r)) (by positivity) (by dsimp only [r]; linarith))
    rw [show (1 / 4 : ℝ) * (4 * r) = r by ring] at h
    have hp : (((1 / 4 : ℝ) ^ n)⁻¹) = (4 : ℝ) ^ n := by rw [← inv_pow]; norm_num
    simpa only [hp] using h
  apply hsmall.trans
  have hcoef : 0 ≤ ((n : ℝ) * (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1))) * (D * δ) := by positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio4 hcoef) (sq_nonneg ‖A.symm b‖)
  convert hh using 1
  ring

end RegularPointCoordinates

end

end OAI
