import OAI.Geometry.RCD.Coordinates.FiniteNormalizerGrowth
import OAI.Geometry.RCD.Metric.UniformVolumeRatio

namespace OAI

/-! # A bounded working frame from a near-identity mean Gram -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every exact normalizer of a mean Gram within one half of the identity
has squared norm at most two. This is uniform in the chosen normalizer. -/
theorem normalizer_norm_sq_le_two_of_sub_id (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (U : E →L[ℝ] SobolevSpace μ hQ) (s : Set X) (hs : MeasurableSet s)
    (A : E ≃L[ℝ] E) (hA : IsExactMeanNormalization μ hQ U s hs A)
    (hgram : ‖sobolevMeanGram μ hQ U s hs - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ‖(A : E →L[ℝ] E)‖ ^ 2 ≤ 2 := by
  have hbound (v : E) : ‖A v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    have hlo := inner_lower_of_sub_id_norm (sobolevMeanGram μ hQ U s hs) hgram (A v)
    rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA] at hlo
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hlo
    linarith
  have hn : ‖(A : E →L[ℝ] E)‖ ≤ Real.sqrt 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hbound v
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_nonneg (A : E →L[ℝ] E)]

/-- The initial splitting error and the fixed Bishop--Gromov volume ratio
construct uniformly bounded working frames at every nearby center. -/
theorem exists_nearby_working_normalizer {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    {p q : X} {R ε : ℝ} {w : X → Euclidean (m + 1)}
    (hR : 0 < R) (hscale : a * (3 * R) ≤ 1) (hε : 0 ≤ ε)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * ε) ≤ 1 / 2)
    (hfirst : FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 * R) ε u w)
    (hq : q ∈ Metric.ball p (R / 4)) :
    ∃ T : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1),
      IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
        (Metric.ball q (R / 2)) measurableSet_ball T ∧
      ‖(T : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))‖ ^ 2 ≤ 2 := by
  let μ := hausdorff (m + 1) X
  let U := sobolevColumnMap μ hX.quadratic u
  have hsub : Metric.ball q (R / 2) ⊆ Metric.ball p (2 * R) := by
    intro x hx
    have hxp := dist_triangle x q p
    have hxq : dist x q < R / 2 := hx
    have hqp : dist q p < R / 4 := hq
    change dist x p < 2 * R
    linarith
  have hratio := nearby_normalization_volume_ratio m hX ha hBG hR hscale hq
  have hnorm : ‖sobolevMeanGram μ hX.quadratic U (Metric.ball q (R / 2)) measurableSet_ball -
      ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ ≤ 1 / 2 :=
    (meanGram_sub_id_norm_le_of_subset μ hX.quadratic u measurableSet_ball hsub
      (ne_of_gt (hX.fullSupport q _ (by positivity)))
      (ne_of_lt (hX.finiteOnBounded _ Metric.isBounded_ball))
      (ne_of_gt (hX.fullSupport p _ (by positivity)))
      (ne_of_lt (hX.finiteOnBounded _ Metric.isBounded_ball))
      (zero_le_one.trans (normalizationVolumeRatio_ge_one m)) hε hratio hfirst.gram).trans hsmall
  obtain ⟨T, hT⟩ := exists_exact_mean_normalization μ hX.quadratic U
    (Metric.ball q (R / 2)) measurableSet_ball (fun v hv => by
      have hlo := inner_lower_of_sub_id_norm _ hnorm v
      have hpos : 0 < (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
        exact mul_pos (by norm_num) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))
      linarith)
  exact ⟨T, hT, normalizer_norm_sq_le_two_of_sub_id μ hX.quadratic U _ measurableSet_ball T hT hnorm⟩

end RegularPointCoordinates

end

end OAI
