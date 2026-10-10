import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.UniformHeatMeanComparison
import OAI.Geometry.RCD.Coordinates.ScaledRegularizer

namespace OAI

/-! # Scale-invariant heat/mean comparison in the original coordinates -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Normalizing the mean at the outer radius is an auxiliary calculation:
the conclusion is the heat comparison for the original coordinates and
their original scalar regularizer. The threshold is uniform in all frames
with the stated fixed working-frame bound. -/
theorem uniform_scaled_rebased_heat_mean_comparison {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) [(hausdorff (m + 1) X).Regular]
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 1) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 1) X) ker)
    {L B V Vlo : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hV : 0 ≤ V) (hVlo : 0 < Vlo)
    (Lambda : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (lambda : ℝ) k, N + 1 ≤ k →
      ∀ (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
        (p : X) (r e : ℝ), 0 < r → r ≤ 1 → (2 : ℝ) ^ k * r ≤ 1 → |lambda| * ((2 : ℝ) ^ k * r) ^ 2 ≤ Lambda →
        0 ≤ e → e ≤ ε →
        ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * e) ≤ 1 / 2 →
      ∀ (T A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1)),
        ‖(T : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))‖ ^ 2 ≤ B →
        IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
          (ball p (2 ^ k * r)) measurableSet_ball T →
        IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
          (ball p r) measurableSet_ball A →
        (∀ j ≤ k, a * (3 * (2 ^ j * r)) ≤ 1) →
        (∀ j ≤ k, ∃ (S : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
          (w : X → Euclidean (m + 1)),
          FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (2 ^ j * r) e
            (transformedColumn (hausdorff (m + 1) X) hX.quadratic u S) w ∧
          IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
            (ball p (2 ^ j * r)) measurableSet_ball S) →
      ∀ (χ : X → ℝ) (hχ : Continuous χ) (hsχ : HasCompactSupport χ),
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        (∀ x ∉ ball p (2 ^ k * r), χ x = 0) →
        (∀ x ∈ ball p (2 ^ N * r), χ x = 1) →
        (∀ j ≤ k, (hausdorff (m + 1) X).real (ball p (2 ^ j * r)) ≤
          V * (2 ^ j * r) ^ (m + 1)) →
        (∀ v : Euclidean (m + 1), ∀ᵐ x ∂(hausdorff (m + 1) X).restrict (ball p (2 ^ k * r)),
          localGamma (hausdorff (m + 1) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v)
            (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v) x ≤ L * ‖v‖ ^ 2) →
        (∀ y, χ y ≠ 0 → Vlo * r ^ (m + 1) ≤
          (hausdorff (m + 1) X).real (ball y r)) →
        ∀ hr : 0 < r,
        ‖(A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint.comp
          ((cutoffHeatGram (hausdorff (m + 1) X) hX.quadratic hk hχ hsχ
            (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
            (sq_pos_of_pos hr) p lambda).comp (A : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))) -
            ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ < η := by
  let μ := hausdorff (m + 1) X
  obtain ⟨N₁, ε, hε, hcompare⟩ := uniform_finite_scale_heat_mean_comparison m hX ha hBG hk hg
    (mul_nonneg hL hB) hV hVlo 0 1 (half_pos hη)
  obtain ⟨N₂, hregularizer⟩ := exists_scaled_regularizer_threshold
    (E := Euclidean (m + 1)) (Lambda := Lambda) hB (half_pos hη)
  refine ⟨max N₁ N₂, ε, hε, ?_⟩
  intro lambda k hkN u p r e hr hr1 hrR hlambda he heε hsmall T A hTnorm hT hA
    hscale hnormal χ hχ hsχ hχrange hχzero hχone hvolume hgradient hvolLower hr'
  let U := sobolevColumnMap μ hX.quadratic u
  let u' := transformedColumn μ hX.quadratic u T
  have hU' : sobolevColumnMap μ hX.quadratic u' = U.comp (T : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)) :=
    sobolevColumnMap_transformed μ hX.quadratic u T
  have hA' := exact_mean_normalization_rebase μ hX.quadratic U T A _ measurableSet_ball hA
  rw [← hU'] at hA'
  have hnormal' : ∀ j ≤ k, ∃ (S : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
      (w : X → Euclidean (m + 1)),
      FirstOrderSplittingOn μ hX.quadratic p (2 ^ j * r) e
        (transformedColumn μ hX.quadratic u' S) w ∧
      IsExactMeanNormalization μ hX.quadratic (sobolevColumnMap μ hX.quadratic u')
        (ball p (2 ^ j * r)) measurableSet_ball S := by
    intro j hj
    obtain ⟨S, w, hfirst, hS⟩ := hnormal j hj
    refine ⟨S.trans T.symm, w, firstOrderSplitting_rebase μ hX.quadratic u T S p _ e w hfirst, ?_⟩
    rw [hU']
    exact exact_mean_normalization_rebase μ hX.quadratic U T S _ measurableSet_ball hS
  have hroot : sobolevMeanGram μ hX.quadratic (sobolevColumnMap μ hX.quadratic u')
      (ball p (2 ^ k * r)) measurableSet_ball = ContinuousLinearMap.id ℝ (Euclidean (m + 1)) := by
    rw [hU']
    exact hT
  have hgradient' v : ∀ᵐ x ∂μ.restrict (ball p (2 ^ k * r)),
      localGamma μ hX.quadratic (sobolevColumnMap μ hX.quadratic u' v)
        (sobolevColumnMap μ hX.quadratic u' v) x ≤ (L * B) * ‖v‖ ^ 2 := by
    filter_upwards [hgradient (T v)] with x hx
    rw [hU', ContinuousLinearMap.comp_apply]
    exact hx.trans (by
      have hm := mul_le_mul_of_nonneg_left
        (norm_apply_sq_le_of_norm_sq_le (T : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)) hTnorm v) hL
      simpa only [mul_assoc, ContinuousLinearEquiv.coe_coe] using hm)
  have hk₁ : N₁ + 1 ≤ k := (Nat.add_le_add_right (le_max_left N₁ N₂) 1).trans hkN
  have hz := hcompare k hk₁ u' p r e hr hr1 hrR he heε hsmall (A.trans T.symm) hA'
    hscale hnormal' hroot χ hχ hsχ hχrange hχzero
    (fun x hx => hχone x (ball_subset_ball
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (le_max_left N₁ N₂)) hr.le) hx))
    hvolume hgradient' hvolLower hr'
  have hnorm := dyadic_normalizer_norm_sq_bound m hX ha hBG u' p hr he hsmall
    (A.trans T.symm) hA' k hscale hnormal' hroot
  have hb := cutoffHeatGram_rebase_norm_le μ hX.quadratic hk hχ hsχ U T A
    (sq_pos_of_pos hr') p lambda hnorm
  have hreg := hregularizer ((2 : ℝ) ^ k * r) lambda hlambda k
    ((le_max_right N₁ N₂).trans ((Nat.le_succ _).trans hkN)) r hr.le le_rfl
    (T : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)) hTnorm
  rw [hU'] at hz
  linarith

end RegularPointCoordinates

end

end OAI
