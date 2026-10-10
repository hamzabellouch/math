import OAI.Geometry.RCD.Coordinates.UniformRegularFlatnessInput
import OAI.Geometry.RCD.Metric.VolumeRigidityInput
import OAI.Geometry.RCD.Metric.VolumeRegime

namespace OAI

/-! # Uniform metric flatness near a regular point from local volume rigidity -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

private def curvatureRadius (K δ : ℝ) : ℝ := min 1 (δ / (|K| + 1))

private theorem curvatureRadius_pos (K : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 < curvatureRadius K δ :=
  lt_min zero_lt_one (div_pos hδ (by positivity))

private theorem curvature_bound_of_radius {K δ t : ℝ} (ht : 0 ≤ t)
    (hsmall : t ≤ curvatureRadius K δ) : -δ ≤ K * t ^ 2 := by
  have ht1 : t ≤ 1 := hsmall.trans (min_le_left _ _)
  have htd : t ≤ δ / (|K| + 1) := hsmall.trans (min_le_right _ _)
  have hbound : t * (|K| + 1) ≤ δ := (le_div_iff₀ (by positivity)).mp htd
  have hs : t ^ 2 ≤ t := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg K)
  have hK := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg t)
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The regular-point volume neighborhood supplies a single neighborhood
whose every sufficiently small ball is pointed close to Euclidean space. -/
theorem regular_uniform_pointed_flatness {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) (hn : 2 ≤ m + 1) {p : X} {a : ℝ}
    (ha : 0 ≤ a) (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 1) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 1) X) (m + 1) p
      (euclideanUnitVolume (m + 1)))
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 1) X)
      (comparisonModelVolume m a) y (euclideanUnitVolume (m + 1)))
    (hrigidity : LocalVolumeRigidityInput hX) {θ : ℝ} (hθ : 0 < θ) :
    ∃ D : ℝ, 0 < D ∧ ∀ q, dist p q ≤ D → ∀ r : ℝ, 0 < r → r ≤ D / 4 →
      ∃ f : X → Euclidean (m + 1), IsPointedApproximation q 0 r 2 θ f := by
  obtain ⟨δ, hδ, happly⟩ := pointed_flatness_of_volume_rigidity hX hn hrigidity hθ
  let ε := min (δ / 2) (1 / 2 : ℝ)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (by linarith)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨D, hD, hDsmall, hvol⟩ := exists_uniform_volume_neighborhood m ha
    (euclideanUnitVolume_pos (m + 1)) hε hε1 (curvatureRadius_pos K hδ)
    hcompact hregular hvolume hBG hdensity
    (fun y r => ne_of_lt (hX.finiteOnBounded (ball y r) isBounded_ball))
  refine ⟨D, hD, ?_⟩
  intro q hq r hr hrD
  have h4rD : 4 * r ≤ D := by linarith
  have hv := hvol q hq (4 * r) (by positivity) h4rD
  have hden : 0 < euclideanUnitVolume (m + 1) * (4 * r) ^ (m + 1) :=
    mul_pos (euclideanUnitVolume_pos _) (pow_pos (by positivity) _)
  have hlo : (1 - δ) * euclideanUnitVolume (m + 1) * (4 * r) ^ (m + 1) ≤
      (hausdorff (m + 1) X).real (ball q (4 * r)) := by
    have h := (abs_le.mp hv).1
    have h' : 1 - δ ≤ (hausdorff (m + 1) X).real (ball q (4 * r)) /
        (euclideanUnitVolume (m + 1) * (4 * r) ^ (m + 1)) := by linarith
    have h'' := (le_div_iff₀ hden).mp h'
    nlinarith
  exact happly q r hr
    (curvature_bound_of_radius (by positivity) (h4rD.trans hDsmall)) hlo

end RegularPointCoordinates

end

end OAI
