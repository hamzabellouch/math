import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.GaussianVolumeTail
import OAI.Geometry.RCD.Metric.VolumeRegime

namespace OAI

/-!
# Uniformly negligible cutoff heat errors near a regular point

The volume lower bound needed for the Gaussian tail estimate is supplied
by the already proved regular-point volume neighborhood, rather than by
an additional analytic assumption.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)

include hk in
/-- At a regular point a single volume neighborhood gives uniform
small-time cutoff-error estimates for every smaller supported cutoff. -/
theorem regular_uniform_heat_cutoff_errors
    (m : ℕ) {a ω R : ℝ} {p : X} (ha : 0 ≤ a) (hω : 0 < ω) (hR : 0 < R)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 1) p)
    (hvolume : EuclideanRescalingVolumeConvergence μ (m + 1) p ω)
    (hBG : BallVolumeComparison μ (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper μ (comparisonModelVolume m a) y ω)
    (hfinite : ∀ y r, μ (ball y r) ≠ ∞) (hg : HasCoordinateHeatBounds μ k) :
    ∃ D : ℝ, 0 < D ∧ D ≤ R ∧ ∀ ρ, 0 < ρ → 2 * ρ ≤ D →
      ∀ C (χ : GoodLaplacianCutoff μ hQ p ρ C) (g : SobolevSpace μ hQ),
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ t, 0 < t → t < δ → ∀ x ∈ ball p (ρ / 2),
            |∫ z, k t x z * cutoffSourceDensity μ hQ g χ.sobolev χ.laplacian z ∂μ| < ε := by
  obtain ⟨D, hD, hDR, hvol⟩ := exists_uniform_volume_neighborhood m ha hω
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hR
    hcompact hregular hvolume hBG hdensity hfinite
  refine ⟨D, hD, hDR, ?_⟩
  intro ρ hρ hρD C χ g ε hε
  apply GoodLaplacianCutoff.heat_error_uniformly_small μ k hQ hk hg χ hρ hD
    (half_pos hω) (m + 1) _ g hε
  intro y _hy hy s hs hsD
  have hpy : dist p y ≤ D := hy.trans hρD
  have hv := hvol y hpy s hs hsD
  have hden : 0 < ω * s ^ (m + 1) := mul_pos hω (pow_pos hs _)
  have hlo : (1 / 2 : ℝ) ≤ μ.real (ball y s) / (ω * s ^ (m + 1)) := by
    linarith [(abs_le.mp hv).1]
  have hmul := (le_div_iff₀ hden).mp hlo
  nlinarith

end RegularPointCoordinates

end

end OAI
