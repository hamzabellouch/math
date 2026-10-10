import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.HeatMeanComparison
import OAI.Geometry.RCD.Heat.UniformHeatComparisonParameters
import OAI.Geometry.RCD.Heat.MissingHeatMass

namespace OAI

/-! # Uniform relative heat/mean comparison on finite normalization ranges -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual heat Gram is close to the identity in every exact small-scale
frame. The thresholds are chosen before the center, radius, harmonic column
and cutoff. Only the finite range up to the working radius is normalized. -/
theorem uniform_finite_scale_heat_mean_comparison {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) [(hausdorff (m + 1) X).Regular]
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 1) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 1) X) ker)
    {L V Vlo : ℝ} (hL : 0 ≤ L) (hV : 0 ≤ V) (hVlo : 0 < Vlo)
    (lambda R : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ k, N + 1 ≤ k →
      ∀ (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
        (p : X) (r e : ℝ), 0 < r → r ≤ 1 → (2 : ℝ) ^ k * r ≤ R →
        0 ≤ e → e ≤ ε →
        ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * e) ≤ 1 / 2 →
      ∀ (A : Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1)),
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
        sobolevMeanGram (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
          (ball p (2 ^ k * r)) measurableSet_ball = ContinuousLinearMap.id ℝ (Euclidean (m + 1)) →
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
  have hfinite : ∀ x r, μ (ball x r) ≠ ∞ :=
    fun x r => ne_of_lt (hX.finiteOnBounded (ball x r) isBounded_ball)
  have hpos : ∀ x r, 0 < r → 0 < μ.real (ball x r) := fun x r hr =>
    ENNReal.toReal_pos (ne_of_gt (hX.fullSupport x r hr)) (hfinite x r)
  obtain ⟨C, B, hC, hB, hgauss⟩ := hg (1 / 2) (by norm_num) (by norm_num)
  let seq := fun j : ℕ => ((2 : ℝ) ^ ((m + 1) + 1)) ^ j * gaussianShellFactor (4 + (1 / 2 : ℝ))⁻¹ j
  have hseq : ∀ j, 0 ≤ seq j := fun j =>
    mul_nonneg (by positivity) (gaussianShellFactor_nonneg _ _)
  have hconst : 0 ≤ (dyadicDirectionConstant m + L + 1) * V * C / Vlo := by
    have hd := dyadicDirectionConstant_nonneg m
    positivity
  obtain ⟨N₁, ε, hε, hparameters⟩ := uniform_heat_comparison_parameters hseq hconst
    (lambda := lambda) (R := R) (B := B) (half_pos hη)
  obtain ⟨N₂, hmass⟩ := missing_heat_mass_uniformly_small μ hX.quadratic hk m ha hBG
    hfinite hpos hg (half_pos hη)
  refine ⟨max N₁ N₂, ε, hε, ?_⟩
  intro k hkN u p r e hr hr1 hrR he heε hsmall A hA hscale hnormal hroot
    χ hχ hsχ hχrange hχzero hχone hvolume hgradient hvolLower hr'
  have hk₁ : N₁ ≤ k := (le_max_left N₁ N₂).trans ((Nat.le_succ _).trans hkN)
  have herror := hparameters k hk₁ e r he heε hr.le hr1 hrR
  have hmissing := hmass (max N₁ N₂) (le_max_right N₁ N₂) p r
    (2 ^ max N₁ N₂ * r) hr hr1 le_rfl χ hχ hsχ hχrange hχone
  have hupper (y : X) : ker (r ^ 2) p y ≤ (C / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / ((4 + 1 / 2) * r ^ 2) + B * r ^ 2) := by
    simpa only [Real.sqrt_sq hr.le] using (hgauss (r ^ 2) (sq_pos_of_pos hr) p y).2
  have hvol (j : ℕ) (hj : j ≤ k) : 0 < μ.real (ball p (2 ^ j * r)) ∧
      μ (ball p (2 ^ j * r)) ≠ ∞ ∧
      μ.real (ball p (2 ^ j * r)) ≤ V * (2 ^ j * r) ^ (m + 1) :=
    ⟨hpos p _ (by positivity), hfinite p _, hvolume j hj⟩
  have hcompare := finite_scale_heat_mean_comparison m hX ha hBG u p hr' he hsmall A hA
    k hscale hnormal hroot hχ hχrange hχzero hL hV hvol hgradient hk hsχ
    hC.le hVlo (by norm_num : (0 : ℝ) < 4 + 1 / 2) hupper hvolLower lambda
  change _ ≤ _ at hcompare
  dsimp only [seq] at herror
  linarith

end RegularPointCoordinates

end

end OAI
