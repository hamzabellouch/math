import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.RebasedHeatMeanComparison
import OAI.Geometry.RCD.Metric.DyadicMassReindex

namespace OAI

/-! # Uniform comparison along one fixed-root dyadic family -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A single fixed coordinate map and its exact dyadic normalizers give
uniform heat comparisons at all sufficiently fine scales. The outer
normalizer is used only for the working-frame calculation. -/
theorem dyadic_heat_mean_comparison {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) [(hausdorff (m + 1) X).Regular]
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 1) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 1) X) ker)
    {L B V Vlo η : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (hV : 0 ≤ V) (hVlo : 0 < Vlo)
    (lambda : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ (R : ℝ), 0 < R → R ≤ 1 → a * (3 * R) ≤ 1 →
      ∀ (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic) (p : X)
        (S : ℕ → Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1)) (e : ℝ),
        0 ≤ e → e ≤ ε →
        ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * e) ≤ 1 / 2 →
        ‖(S 0 : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))‖ ^ 2 ≤ B →
        (∀ i, IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
          (ball p (R / 2 ^ i)) measurableSet_ball (S i)) →
        (∀ i, ∃ w : X → Euclidean (m + 1),
          FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (R / 2 ^ i) e
            (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i)) w) →
      ∀ (χ : X → ℝ) (hχ : Continuous χ) (hsχ : HasCompactSupport χ),
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x ∉ ball p R, χ x = 0) →
        (∀ x ∈ ball p (R / 4), χ x = 1) →
        (∀ i, (hausdorff (m + 1) X).real (ball p (R / 2 ^ i)) ≤ V * (R / 2 ^ i) ^ (m + 1)) →
        (∀ v : Euclidean (m + 1), ∀ᵐ x ∂(hausdorff (m + 1) X).restrict (ball p R),
          localGamma (hausdorff (m + 1) X) hX.quadratic
            (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v)
            (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u v) x ≤ L * ‖v‖ ^ 2) →
        (∀ i y, χ y ≠ 0 → Vlo * (R / 2 ^ i) ^ (m + 1) ≤
          (hausdorff (m + 1) X).real (ball y (R / 2 ^ i))) →
        ∀ i, N ≤ i → ∀ hi : 0 < R / (2 : ℝ) ^ i,
          ‖(S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint.comp
            ((cutoffHeatGram (hausdorff (m + 1) X) hX.quadratic hk hχ hsχ
              (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
              (sq_pos_of_pos hi) p lambda).comp (S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))) -
            ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ < η := by
  obtain ⟨N, ε, hε, hcompare⟩ := uniform_rebased_heat_mean_comparison m hX ha hBG hk hg
    hL hB hV hVlo lambda 1 hη
  refine ⟨N + 2, ε, hε, ?_⟩
  intro R hR hR1 hscale u p S e he heε hsmall hS0 hexact hfirst χ hχ hsχ hχrange hχzero hχone
    hvolume hgradient hvolLower i hi hi'
  have hroot : (2 : ℝ) ^ i * (R / (2 : ℝ) ^ i) = R := by field_simp
  have hradius (j : ℕ) (hj : j ≤ i) :
      (2 : ℝ) ^ j * (R / (2 : ℝ) ^ i) = R / (2 : ℝ) ^ (i - j) := by
    simpa only [Nat.sub_sub_self hj] using
      outward_radius_eq_ancestor hroot (Nat.sub_le i j)
  have hrR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  apply hcompare i (by omega) u p (R / 2 ^ i) e hi' (hrR.trans hR1)
    (by simpa only [hroot] using hR1) he heε hsmall
    (S 0) (S i) hS0
  · rw [hroot]
    simpa only [pow_zero, div_one] using hexact 0
  · exact hexact i
  · intro j hj
    rw [hradius j hj]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (div_le_self hR.le (one_le_pow₀ (by norm_num))) (by norm_num : (0 : ℝ) ≤ 3)) ha).trans hscale
  · intro j hj
    rw [hradius j hj]
    obtain ⟨w, hw⟩ := hfirst (i - j)
    exact ⟨S (i - j), w, hw, hexact (i - j)⟩
  · exact hχrange
  · simpa only [hroot] using hχzero
  · intro x hx
    apply hχone x
    apply ball_subset_ball _ hx
    rw [hradius N (by omega)]
    have hpow : (4 : ℝ) ≤ 2 ^ (i - N) := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ i - N by omega)
      norm_num at h ⊢
      exact h
    exact div_le_div_of_nonneg_left hR.le (by norm_num) hpow
  · intro j hj
    rw [hradius j hj]
    exact hvolume (i - j)
  · simpa only [hroot] using hgradient
  · exact hvolLower i
  · exact hi'

end RegularPointCoordinates

end

end OAI
