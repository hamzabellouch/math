import OAI.Geometry.RCD.Heat.FiniteScaleHeatError

namespace OAI

/-! # Relative heat/mean comparison for the normalized RCD harmonic column

All errors come from the actual finite-scale splitting, the raw gradient
bound and the cutoff kernel. The missing heat mass and scalar regularizer
contribute explicitly to the estimate.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The finite normalization data give relative heat Gram control in the
same exact frame, with a small prefix and a vanishing Gaussian tail. -/
theorem finite_scale_heat_mean_comparison {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
    [(hausdorff (m + 1) X).Regular]
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
      (ball p (2 ^ k * r)) measurableSet_ball = ContinuousLinearMap.id ℝ (Euclidean (m + 1)))
    {χ : X → ℝ} (hχ : Continuous χ) (hχrange : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ ball p (2 ^ k * r), χ x = 0)
    {L V : ℝ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    (hvolume : ∀ j ≤ k, 0 < (hausdorff (m + 1) X).real (ball p (2 ^ j * r)) ∧
      hausdorff (m + 1) X (ball p (2 ^ j * r)) ≠ ∞ ∧
      (hausdorff (m + 1) X).real (ball p (2 ^ j * r)) ≤ V * (2 ^ j * r) ^ (m + 1))
    (hgradient : ∀ v : Euclidean (m + 1), ∀ᵐ x ∂(hausdorff (m + 1) X).restrict (ball p (2 ^ k * r)),
      localGamma (hausdorff (m + 1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v)
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v) x ≤ L * ‖v‖ ^ 2)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 1) X) hX.quadratic ker)
    (hsχ : HasCompactSupport χ) {C Vlo D B : ℝ}
    (hC : 0 ≤ C) (hVlo : 0 < Vlo) (hD : 0 < D)
    (hupper : ∀ y, ker (r ^ 2) p y ≤ (C / (hausdorff (m + 1) X).real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / (D * r ^ 2) + B * r ^ 2))
    (hvolLower : ∀ y, χ y ≠ 0 → Vlo * r ^ (m + 1) ≤
      (hausdorff (m + 1) X).real (ball y r)) (lambda : ℝ) :
    let a := fun j : ℕ => ((2 : ℝ) ^ ((m + 1) + 1)) ^ j * gaussianShellFactor D⁻¹ j
    let error := ((dyadicDirectionConstant m + L + 1) * V * C / Vlo) *
      Real.exp (B * r ^ 2) * (ε * (∑' j, a j) + ∑' j, a (j + (k + 1)))
    ‖(A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint.comp
      ((cutoffHeatGram (hausdorff (m + 1) X) hX.quadratic hk hχ hsχ
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (sq_pos_of_pos hr) p lambda).comp
          (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))) -
        ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ ≤
      error + |(∫ y, χ y * ker (r ^ 2) p y ∂(hausdorff (m + 1) X)) - 1| +
        |lambda * r ^ 2| * 2 ^ k := by
  let μ := hausdorff (m + 1) X
  let U := sobolevColumnMap μ hX.quadratic u
  let a := fun j : ℕ => ((2 : ℝ) ^ ((m + 1) + 1)) ^ j * gaussianShellFactor D⁻¹ j
  let budget := ε * (∑' j, a j) + ∑' j, a (j + (k + 1))
  let error := ((dyadicDirectionConstant m + L + 1) * V * C / Vlo) * Real.exp (B * r ^ 2) * budget
  have hbase : 0 ≤ (2 : ℝ) ^ ((m + 1) + 1) := by positivity
  have hconst : 0 ≤ dyadicDirectionConstant m + L + 1 := by
    linarith [dyadicDirectionConstant_nonneg m]
  have hapos (j : ℕ) : 0 ≤ a j := mul_nonneg (pow_nonneg hbase _) (gaussianShellFactor_nonneg _ _)
  have hbudget : 0 ≤ budget := add_nonneg (mul_nonneg hε (tsum_nonneg hapos))
    (tsum_nonneg fun j => hapos (j + (k + 1)))
  have herror : 0 ≤ error := by dsimp [error]; positivity
  have hdir (v : Euclidean (m + 1)) :
      (∫ y, (χ y * ker (r ^ 2) p y) * |localGamma μ hX.quadratic (U (A v)) (U (A v)) y - ‖v‖ ^ 2| ∂μ) ≤
        error * ‖v‖ ^ 2 := by
    have hb (j : ℕ) := finite_scale_cutoff_budget m hX ha hBG u p hr hε hsmall A hA k
      hscale hnormal hroot hχ hχrange hχzero hL hV hvolume hgradient v j
    have hh := finite_scale_heat_direction_error μ hX.quadratic hk hχ hsχ (U (A v)) (‖v‖ ^ 2)
      (m + 1) (k + 1) p hr hC hVlo hD
      (show 0 ≤ (dyadicDirectionConstant m + L + 1) * V * ‖v‖ ^ 2 by positivity)
      hbase hε hχrange hupper hvolLower
      (fun j => by simpa only [mul_assoc, mul_comm, mul_left_comm] using hb j)
    convert hh using 1
    dsimp [error, budget, a]
    ring
  have he := cutoffHeatGram_conjugated_norm_le_of_directional μ hX.quadratic hk hχ hsχ
    U A (fun y => (hχrange y).1) (sq_pos_of_pos hr) p lambda herror hdir
  have hn := dyadic_normalizer_norm_sq_bound m hX ha hBG u p hr hε hsmall A hA
    k hscale hnormal hroot
  have hreg := mul_le_mul_of_nonneg_left hn (abs_nonneg (lambda * r ^ 2))
  dsimp [error, budget, a, μ, U] at he
  linarith

end RegularPointCoordinates

end

end OAI
