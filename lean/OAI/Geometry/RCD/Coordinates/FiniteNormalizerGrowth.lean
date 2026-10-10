import OAI.Geometry.RCD.Coordinates.DyadicNormalizedError

namespace OAI

/-! # Polynomial norm control of exact normalizers over a finite range -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Relative growth of means gives the squared norm bound for the exact
normalizer at the smaller scale. The larger mean is already normalized. -/
theorem normalizer_norm_sq_le_of_mean_growth (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (U : E →L[ℝ] SobolevSpace μ hQ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (A : E ≃L[ℝ] E) (hA : IsExactMeanNormalization μ hQ U s hs A)
    (htId : sobolevMeanGram μ hQ U t ht = ContinuousLinearMap.id ℝ E)
    {B : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ v : E, ⟪v, sobolevMeanGram μ hQ U t ht v⟫_ℝ ≤
      B * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ) :
    ‖(A : E →L[ℝ] E)‖ ^ 2 ≤ B := by
  have hv (v : E) : ‖A v‖ ^ 2 ≤ B * ‖v‖ ^ 2 := by
    have hh := hgrowth (A v)
    rw [htId, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] at hh
    rw [meanGram_energy_of_exact_normalization μ hQ U s hs A hA] at hh
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
  have hnorm : ‖(A : E →L[ℝ] E)‖ ≤ Real.sqrt B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hh := hv v
    have hp : 0 ≤ Real.sqrt B * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    change ‖A v‖ ≤ Real.sqrt B * ‖v‖
    apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    rwa [mul_pow, Real.sq_sqrt hB]
  nlinarith [Real.sq_sqrt hB, norm_nonneg (A : E →L[ℝ] E)]

omit [CompleteSpace E] in
/-- The frame growth bound yields a bound for every transformed direction. -/
theorem norm_apply_sq_le_of_norm_sq_le (A : E →L[ℝ] E) {B : ℝ}
    (hA : ‖A‖ ^ 2 ≤ B) (v : E) : ‖A v‖ ^ 2 ≤ B * ‖v‖ ^ 2 := by
  calc
    _ ≤ (‖A‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm v) 2
    _ = ‖A‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hA (sq_nonneg _)

/-- A normalized working-scale mean gives polynomial growth of every
smaller exact frame from the proved adjacent mean comparisons. -/
theorem dyadic_normalizer_norm_sq_bound {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
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
    (hroot : sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
      (Metric.ball p (2 ^ k * r)) measurableSet_ball =
        ContinuousLinearMap.id ℝ (Euclidean (m + 1))) :
    ‖(A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))‖ ^ 2 ≤ 2 ^ k := by
  apply normalizer_norm_sq_le_of_mean_growth _ _ _ (Metric.ball p r)
    (Metric.ball p (2 ^ k * r)) measurableSet_ball measurableSet_ball A hA hroot
    (pow_nonneg (by norm_num) k)
  intro v
  simpa only [pow_zero, one_mul] using
    (dyadic_mean_growth m hX ha hBG u p hr hε hsmall k hscale hnormal v).1

end RegularPointCoordinates

end

end OAI
