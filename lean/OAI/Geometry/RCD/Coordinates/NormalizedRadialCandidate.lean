import OAI.Geometry.RCD.Coordinates.FramedRadialCandidate
import OAI.Geometry.RCD.Coordinates.RadialFrameLocalization
import OAI.Geometry.RCD.Coordinates.DyadicRadialFitEstimates

namespace OAI

/-! # Quantitative comparison with the original centered coordinate function -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
  (hQ : QuadraticCheegerEnergy μ)

/-- The genuine radial derivative is close to the centered original
coordinate function in the same inverse-frame norm used by the fits. -/
theorem DyadicDistanceReplacements.normalized_radial_candidate
    {n : ℕ} {κ r0 B J C omega δ Cχ : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (homega : 0 < omega) (hδ : 0 ≤ δ)
    (hδ1 : radialNormalizationRestrictionConstant n * δ ≤ 1) (hCχ : 0 ≤ Cχ)
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ 2 * distanceSourceRadius r0 i →
      |μ.real (ball p t) / (omega * t ^ n) - 1| ≤ 1 / 4)
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (V W : X → Euclidean n)
    (hV : ContinuousOn V (ball p (2 * distanceSourceRadius r0 i)))
    (hu : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[
      μ.restrict (ball p (2 * distanceSourceRadius r0 i))] fun x => V x j)
    (hfirst : FirstOrderSplittingOn μ hQ p (2 * distanceSourceRadius r0 i) δ
      (transformedColumn μ hQ u N) W)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (W x - W p)))
    (χ : GoodLaplacianCutoff μ hQ p (distanceSourceRadius r0 i / 64) Cχ)
    (b : Euclidean n) {L : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (ball p (distanceSourceRadius r0 i / 64)),
      localGamma μ hQ (sobolevColumnMap μ hQ u b) (sobolevColumnMap μ hQ u b) x ≤ L) :
    let r := distanceSourceRadius r0 i / 64
    let hfin : μ (ball p r) ≠ ∞ := ne_of_lt
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall p r).measure_lt_top)
    ‖normalizeLocalL2 μ (ball p r) hfin
      (radialPairingLp μ hQ (ball p r) (T.distanceDatum μ hQ i)
        (sobolevColumnMap μ hQ u b) ha -
        SobolevSpace.restrictLp μ hQ (ball p r)
          (centeredAffineSobolev μ hQ u (T.cutoff i).sobolev (V p) b))‖ ^ 2 ≤
      radialFitQualitativeConstant n Cχ * δ * r ^ 2 * ‖N.symm b‖ ^ 2 := by
  dsimp only
  let s := distanceSourceRadius r0 i
  let r := s / 64
  let D := radialNormalizationRestrictionConstant n
  have hs : 0 < s := distanceSourceRadius_pos S.radius_pos i
  have hr : 0 < r := by dsimp only [r]; positivity
  have hD : 1 ≤ D := radialNormalizationRestrictionConstant_ge_one n
  have hε : 0 ≤ D * δ := mul_nonneg (zero_le_one.trans hD) hδ
  obtain ⟨hlocal, hvol, hratio⟩ := localize_radial_frame μ hQ hs homega hδ hquarter
    (transformedColumn μ hQ u N) W hfirst
  have hsub : ball p (4 * r) ⊆ ball p (2 * s) := ball_subset_ball (by dsimp only [r]; linarith)
  have hη : SobolevSpace.toLp μ hQ (T.cutoff i).sobolev =ᵐ[μ.restrict (ball p (4 * r))]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (T.cutoff i).representative,
      ae_restrict_mem measurableSet_ball] with x hx hxr
    exact hx.trans ((T.cutoff i).one x
      ((ball_subset_ball (show 4 * r ≤ 4 * s by dsimp only [r]; linarith)) hxr))
  have hmetric' := hmetric.mono_error (show δ ≤ D * δ by nlinarith)
  have herr := T.framed_radial_candidate μ hQ i hε hδ1 hCχ u N V W
    (hV.mono hsub) (fun j => ae_restrict_of_ae_restrict_of_subset hsub (hu j)) hlocal hmetric'
    (T.cutoff i).sobolev hη χ hvol b
  dsimp only at herr
  let q := T.distanceDatum μ hQ i
  let H := centeredAffineSobolev μ hQ u (T.cutoff i).sobolev (V p) b
  let t := radialPairingLp μ hQ (ball p r) q (sobolevColumnMap μ hQ u b) ha
  let v := SobolevSpace.restrictLp μ hQ (ball p r) H
  have heq : (fun x => ((t - v) x) ^ 2) =ᵐ[μ.restrict (ball p r)]
      fun x => (localGamma μ hQ q (sobolevColumnMap μ hQ u b) x - SobolevSpace.toLp μ hQ H x) ^ 2 := by
    filter_upwards [Lp.coeFn_sub t v,
      radialPairingLp_representative μ hQ (ball p r) q (sobolevColumnMap μ hQ u b) ha,
      SobolevSpace.restrictLp_coe μ hQ (ball p r) H] with x hsub ht hv
    simp only [hsub, Pi.sub_apply]
    change (t x - v x) ^ 2 = _
    rw [ht, hv]
  rw [normalizeLocalL2_norm_sq, integral_congr_ae heq]
  have hb := mul_le_mul_of_nonneg_left herr
    (inv_nonneg.mpr (show 0 ≤ μ.real (ball p r) from measureReal_nonneg))
  apply hb.trans
  have hcoef : 0 ≤ ((n : ℝ) * (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1))) *
      (D * δ) * r ^ 2 * ‖N.symm b‖ ^ 2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hratio hcoef
  convert hh using 1 <;> dsimp only [radialFitQualitativeConstant, D] <;> ring

end RegularPointCoordinates

end

end OAI
