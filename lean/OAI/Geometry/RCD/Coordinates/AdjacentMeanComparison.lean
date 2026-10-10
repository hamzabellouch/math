import OAI.Geometry.RCD.Coordinates.ExactNormalizationComparison
import OAI.Geometry.RCD.Metric.UniformVolumeRatio

namespace OAI

/-! # Adjacent-scale relative mean comparison from the published splitting input -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A fixed dimensional Bishop--Gromov ratio controls the restriction to
half radius. No interscale transformation bound is assumed. -/
theorem normalized_adjacent_mean_comparison {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    {p : X} {r ε : ℝ} {w : X → Euclidean (m + 1)}
    (hr : 0 < r) (hscale : a * (3 * (r / 2)) ≤ 1) (hε : 0 ≤ ε)
    (hfirst : FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p r ε
      (transformedColumn (hausdorff (m + 1) X) hX.quadratic u A) w)
    (hexact : IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p r) measurableSet_ball A)
    (v : Euclidean (m + 1)) :
    (1 - ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε)) *
        ⟪v, sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p r) measurableSet_ball v⟫_ℝ ≤
      ⟪v, sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p (r / 2)) measurableSet_ball v⟫_ℝ ∧
    ⟪v, sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p (r / 2)) measurableSet_ball v⟫_ℝ ≤
      (1 + ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε)) *
        ⟪v, sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p r) measurableSet_ball v⟫_ℝ := by
  let μ := hausdorff (m + 1) X
  have hratio := nearby_normalization_volume_ratio m hX ha hBG (half_pos hr) hscale
    (show p ∈ ball p ((r / 2) / 4) by simpa only [mem_ball, dist_self] using (by positivity : (0 : ℝ) < (r / 2) / 4))
  have hsmall : μ.real (ball p ((r / 2) / 2)) ≤ μ.real (ball p (r / 2)) :=
    measureReal_mono (ball_subset_ball (by linarith))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hC : 0 ≤ normalizationVolumeRatio m := le_trans zero_le_one (normalizationVolumeRatio_ge_one m)
  have hvol : μ.real (ball p r) ≤ normalizationVolumeRatio m * μ.real (ball p (r / 2)) := by
    have htwo : 2 * (r / 2) = r := by ring
    rw [htwo] at hratio
    exact hratio.trans (mul_le_mul_of_nonneg_left hsmall hC)
  exact exact_normalization_subball_bounds μ hX.quadratic u A hfirst hexact
    (ball p (r / 2)) measurableSet_ball (ball_subset_ball (by linarith))
    (ne_of_gt (hX.fullSupport p (r / 2) (half_pos hr)))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (ne_of_gt (hX.fullSupport p r hr))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) hC hε hvol v

end RegularPointCoordinates

end

end OAI
