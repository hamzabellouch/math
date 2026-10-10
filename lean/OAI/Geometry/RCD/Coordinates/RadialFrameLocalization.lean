import OAI.Geometry.RCD.Coordinates.NormalizedFrameRadialSmallness

namespace OAI

/-! # Localizing the actual normalizing frame to the radial testing region -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem localize_radial_frame {n : ℕ} {s omega δ : ℝ} {p : X}
    (hs : 0 < s) (homega : 0 < omega) (hδ : 0 ≤ δ)
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ 2 * s →
      |μ.real (ball p t) / (omega * t ^ n) - 1| ≤ 1 / 4)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn μ hQ p (2 * s) δ u v) :
    FirstOrderSplittingOn μ hQ p (4 * (s / 64))
      (radialNormalizationRestrictionConstant n * δ) u v ∧
    0 < μ.real (ball p (4 * (s / 64))) ∧
    μ.real (ball p (4 * (s / 64))) / μ.real (ball p (s / 64)) ≤
      (5 / 3 : ℝ) * (4 : ℝ) ^ n := by
  let r := s / 64
  let D := radialNormalizationRestrictionConstant n
  have hr : 0 < r := by dsimp only [r]; positivity
  have hD : 1 ≤ D := radialNormalizationRestrictionConstant_ge_one n
  have hv (t : ℝ) (ht : 0 < t) (hts : t ≤ 2 * s) : 0 < μ.real (ball p t) :=
    (quarter_volume_bounds ht homega (hquarter t ht hts)).1
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
  refine ⟨hlocal, hv (4 * r) (by positivity) (by dsimp only [r]; linarith), ?_⟩
  have h := radial_fraction_volume_ratio (show 0 < 4 * r by positivity)
    (by norm_num : (0 : ℝ) < 1 / 4) homega
    (hquarter (4 * r) (by positivity) (by dsimp only [r]; linarith))
    (hquarter ((1 / 4 : ℝ) * (4 * r)) (by positivity) (by dsimp only [r]; linarith))
  rw [show (1 / 4 : ℝ) * (4 * r) = r by ring] at h
  have hp : (((1 / 4 : ℝ) ^ n)⁻¹) = (4 : ℝ) ^ n := by rw [← inv_pow]; norm_num
  simpa only [hp] using h

end RegularPointCoordinates

end

end OAI
