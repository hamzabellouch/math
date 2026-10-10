import OAI.Geometry.RCD.Heat.DyadicHeatFamily
import OAI.Geometry.RCD.Heat.SlowHeatGrowth

namespace OAI

/-! # Slow growth for one actual dyadic heat family -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Exact normalizers and the proved heat-to-mean comparison give the
adjacent 9/8 bound without changing the original coordinate frame. -/
theorem dyadic_heat_step_of_conjugated_comparison {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) [(hausdorff (m + 1) X).Regular]
    {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 1) X) hX.quadratic ker)
    (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
    (S : ℕ → Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
    {p : X} {ρ Ccut R lambda e : ℝ}
    (χ : GoodLaplacianCutoff (hausdorff (m + 1) X) hX.quadratic p ρ Ccut)
    (hR : 0 < R) (hlambda : 0 < lambda) (he : 0 ≤ e)
    (hscale : a * (3 * R) ≤ 1)
    (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * e) ≤ 1 / 64)
    (hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
      (ball p (R / 2 ^ i)) measurableSet_ball (S i))
    (hfirst : ∀ i, ∃ w : X → Euclidean (m + 1),
      FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (R / 2 ^ i) e
        (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i)) w)
    (J : ℕ)
    (hclose : ∀ i, J ≤ i →
      ‖(S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).adjoint.comp
        ((dyadicHeatGram (hausdorff (m + 1) X) hX.quadratic hk
          (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) χ hR hlambda i :
            Euclidean (m + 1) →L[ℝ] Euclidean (m + 1)).comp
          (S i : Euclidean (m + 1) →L[ℝ] Euclidean (m + 1))) -
        ContinuousLinearMap.id ℝ (Euclidean (m + 1))‖ ≤ 1 / 64) :
    ∀ i, J ≤ i → ∀ v,
      ⟪v, dyadicHeatGram (hausdorff (m + 1) X) hX.quadratic hk
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) χ hR hlambda i v⟫_ℝ ≤
      (9 / 8 : ℝ) * ⟪v, dyadicHeatGram (hausdorff (m + 1) X) hX.quadratic hk
        (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) χ hR hlambda (i + 1) v⟫_ℝ := by
  intro i hi v
  have hr : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hnext : R / (2 : ℝ) ^ (i + 1) = (R / (2 : ℝ) ^ i) / 2 := by
    rw [pow_succ, div_mul_eq_div_div]
  have hs : a * (3 * ((R / (2 : ℝ) ^ i) / 2)) ≤ 1 := by
    have hle : (R / (2 : ℝ) ^ i) / 2 ≤ R :=
      (div_le_self hr.le (by norm_num)).trans (div_le_self hR.le (one_le_pow₀ (by norm_num)))
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by norm_num)) ha).trans hscale
  obtain ⟨w, hw⟩ := hfirst i
  apply conjugated_adjacent_heat_step m hX ha hBG u (S i) (S (i + 1)) hr hs he hsmall hw
    (hexact i) (by simpa only [hnext] using hexact (i + 1))
    _ _ (hclose i hi) (hclose (i + 1) (by omega)) v

end RegularPointCoordinates

end

end OAI
