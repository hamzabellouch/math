import OAI.Geometry.RCD.Heat.DyadicHeatStability

namespace OAI

/-! # Four-scale control of the actual dyadic mean Grams -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

def dyadicMeanGram (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (p : X) (R : ℝ) (i : ℕ) :
    Euclidean n →L[ℝ] Euclidean n :=
  sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) (ball p (R / 2 ^ i)) measurableSet_ball

variable {K : ℝ} (m : ℕ) (hX : NoncollapsedRCD K (m + 1) X)
  {a : ℝ} (ha : 0 ≤ a)
  (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
  (u : Fin (m + 1) → SobolevSpace (hausdorff (m + 1) X) hX.quadratic)
  (S : ℕ → Euclidean (m + 1) ≃L[ℝ] Euclidean (m + 1))
  {p : X} {R e : ℝ} (hR : 0 < R) (he : 0 ≤ e) (hscale : a * (3 * R) ≤ 1)
  (hsmall : ((m + 1 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio m * e) ≤ 1 / 64)
  (hexact : ∀ i, IsExactMeanNormalization (hausdorff (m + 1) X) hX.quadratic
    (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u)
    (ball p (R / 2 ^ i)) measurableSet_ball (S i))
  (hfirst : ∀ i, ∃ w : X → Euclidean (m + 1),
    FirstOrderSplittingOn (hausdorff (m + 1) X) hX.quadratic p (R / 2 ^ i) e
      (transformedColumn (hausdorff (m + 1) X) hX.quadratic u (S i)) w)

include ha hBG hR he hscale hsmall hexact hfirst in
/-- The actual means have the same slow one-step growth as the heat metrics. -/
theorem dyadic_mean_slow_step (i : ℕ) (v : Euclidean (m + 1)) :
    ⟪v, dyadicMeanGram (hausdorff (m + 1) X) hX.quadratic u p R i v⟫_ℝ ≤
      (9 / 8 : ℝ) * ⟪v, dyadicMeanGram (hausdorff (m + 1) X) hX.quadratic u p R (i + 1) v⟫_ℝ := by
  have hr : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
  have hs : a * (3 * ((R / (2 : ℝ) ^ i) / 2)) ≤ 1 := by
    have hle : (R / (2 : ℝ) ^ i) / 2 ≤ R :=
      (div_le_self hr.le (by norm_num)).trans (div_le_self hR.le (one_le_pow₀ (by norm_num)))
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by norm_num)) ha).trans hscale
  obtain ⟨w, hw⟩ := hfirst i
  have h := (normalized_adjacent_mean_comparison m hX ha hBG u (S i) hr hs he hw (hexact i) v).1
  have hp := (sobolevMeanGram_isPositive (hausdorff (m + 1) X) hX.quadratic
    (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p (R / 2 ^ i)) measurableSet_ball).inner_nonneg_right v
  have hm := mul_le_mul_of_nonneg_right hsmall hp
  have hnext : R / (2 : ℝ) ^ (i + 1) = (R / (2 : ℝ) ^ i) / 2 := by
    rw [pow_succ, div_mul_eq_div_div]
  simp only [dyadicMeanGram, hnext]
  nlinarith only [h, hm, hp]

include ha hBG hR he hscale hsmall hexact hfirst in
/-- Moving four dyadic scales inward costs less than two. This is the
enlargement used by the local Bochner cutoff estimate. -/
theorem dyadic_mean_four_le_two (i : ℕ) (hi : 4 ≤ i) (v : Euclidean (m + 1)) :
    ⟪v, dyadicMeanGram (hausdorff (m + 1) X) hX.quadratic u p R (i - 4) v⟫_ℝ ≤
      2 * ⟪v, dyadicMeanGram (hausdorff (m + 1) X) hX.quadratic u p R i v⟫_ℝ := by
  have h := geometric_form_growth
    (dyadicMeanGram (hausdorff (m + 1) X) hX.quadratic u p R)
    (by norm_num : (0 : ℝ) ≤ 9 / 8)
    (dyadic_mean_slow_step m hX ha hBG u S hR he hscale hsmall hexact hfirst)
    (Nat.sub_le i 4) v
  have heq : i - (i - 4) = 4 := by omega
  rw [heq] at h
  have hp := (sobolevMeanGram_isPositive (hausdorff (m + 1) X) hX.quadratic
    (sobolevColumnMap (hausdorff (m + 1) X) hX.quadratic u) (ball p (R / 2 ^ i)) measurableSet_ball).inner_nonneg_right v
  change 0 ≤ ⟪v, dyadicMeanGram (hausdorff (m + 1) X) hX.quadratic u p R i v⟫_ℝ at hp
  norm_num at h
  linarith

end RegularPointCoordinates

end

end OAI
