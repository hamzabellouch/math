import OAI.Geometry.RCD.Coordinates.DyadicMeanControl
import OAI.Geometry.RCD.Coordinates.NormalizedDirectionError

namespace OAI

/-! # Uniform directional errors in a fixed dyadic normalizing frame -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Outward mean comparisons become a norm estimate in the initial exact frame. -/
theorem dyadic_normalized_mean_bound {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (p : X) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε) ≤ 1 / 2)
    (A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    (hA : IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p r) measurableSet_ball A)
    (k : ℕ) (hscale : ∀ j ≤ k, a * (3 * (2 ^ j * r)) ≤ 1)
    (hnormal : ∀ j ≤ k, ∃ (S : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
      (w : X → Euclidean (m + 1)),
      FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 ^ j * r) ε
        (transformedColumn (hausdorff (m + 1) X) hX.quadratic u S) w ∧
      IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
        (ball p (2 ^ j * r)) measurableSet_ball S) :
    ‖sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
      ((sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u).comp (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)))
      (ball p (2 ^ k * r)) measurableSet_ball -
      ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ ≤
        2 * (((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε)) * (2 ^ k - 1) := by
  apply normalized_mean_relative_norm_le _ _ _ (ball p r) (ball p (2 ^ k * r))
    measurableSet_ball measurableSet_ball A hA
  · have hratio : 0 ≤ normalizationVolumeRatio m :=
      zero_le_one.trans (normalizationVolumeRatio_ge_one m)
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    positivity
  · intro v
    simpa only [pow_zero, one_mul] using
      (dyadic_mean_growth m hX ha hBG u p hr hε hsmall k hscale hnormal v).2

/-- The coefficient in the directional estimate grows at most like `2^k`,
while retaining the original splitting error. -/
theorem dyadic_error_coefficient_le {n C ε : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hsmall : n ^ 2 * (C * ε) ≤ 1 / 2) (k : ℕ) :
    (n ^ 2 * ε) * (1 + 2 * (n ^ 2 * (C * ε)) * (2 ^ k - 1)) +
      2 * (n ^ 2 * (C * ε)) * (2 ^ k - 1) ≤
      (n ^ 2 + 2 * (n ^ 2 * C)) * ε * 2 ^ k := by
  have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hbound : 1 + 2 * (n ^ 2 * (C * ε)) * (2 ^ k - 1) ≤ 2 ^ k := by
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hbound (mul_nonneg (sq_nonneg n) hε)
  have h2 : 2 * (n ^ 2 * (C * ε)) * (2 ^ k - 1) ≤
      2 * (n ^ 2 * (C * ε)) * 2 ^ k := by
    apply mul_le_mul_of_nonneg_left (by linarith)
    positivity
  nlinarith

/-- Every finite outward dyadic ball has a directional L1 error bounded
by the initial splitting tolerance times an explicit geometric factor. -/
theorem dyadic_normalized_directional_error {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (p : X) {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε) ≤ 1 / 2)
    (A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    (hA : IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p r) measurableSet_ball A)
    (k : ℕ) (hscale : ∀ j ≤ k, a * (3 * (2 ^ j * r)) ≤ 1)
    (hnormal : ∀ j ≤ k, ∃ (S : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
      (w : X → Euclidean (m + 1)),
      FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 ^ j * r) ε
        (transformedColumn (hausdorff (m + 1) X) hX.quadratic u S) w ∧
      IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
        (ball p (2 ^ j * r)) measurableSet_ball S)
    (hvolume : 0 < (hausdorff (m + 1) X).real (ball p (2 ^ k * r)))
    (hfinite : hausdorff (m + 1) X (ball p (2 ^ k * r)) ≠ ⊤)
    (v : Euclidean (m + 1)) :
    (∫ x in ball p (2 ^ k * r),
      |localGamma (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u (A v))
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u (A v)) x - ‖v‖ ^ 2|
          ∂(hausdorff (m + 1) X)) ≤
      ((((m + 1 : ℕ) : ℝ) ^ 2 +
        2 * (((m + 1 : ℕ) : ℝ) ^ 2 * normalizationVolumeRatio m)) * ε * 2 ^ k) *
          (hausdorff (m + 1) X).real (ball p (2 ^ k * r)) * ‖v‖ ^ 2 := by
  obtain ⟨S, w, hfirst, hexact⟩ := hnormal k le_rfl
  have hmean := dyadic_normalized_mean_bound m hX ha hBG u p hr hε hsmall A hA
    k hscale hnormal
  have he := changed_frame_directional_error (hausdorff (m + 1) X) hX.quadratic u p
    (2 ^ k * r) S A hε hfirst hexact hvolume hfinite hmean v
  have hc := dyadic_error_coefficient_le
    (zero_le_one.trans (normalizationVolumeRatio_ge_one m)) hε hsmall k
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc hvolume.le) (sq_nonneg _))

end RegularPointCoordinates

end

end OAI
