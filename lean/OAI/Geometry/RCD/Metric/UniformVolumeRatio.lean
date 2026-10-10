import OAI.Geometry.RCD.Metric.ComparisonModel

namespace OAI

/-! # A dimensional volume-ratio bound for nearby balls -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

def normalizationVolumeRatio (m : ℕ) : ℝ := Real.cosh 1 ^ m * 6 ^ (m + 1)

theorem normalizationVolumeRatio_ge_one (m : ℕ) : 1 ≤ normalizationVolumeRatio m := by
  have hc : 1 ≤ Real.cosh 1 ^ m := one_le_pow₀ (Real.one_le_cosh 1)
  have hs : (1 : ℝ) ≤ 6 ^ (m + 1) := one_le_pow₀ (by norm_num)
  dsimp [normalizationVolumeRatio]
  nlinarith

/-- Bishop--Gromov supplies the volume loss used to localize splitting
maps; the constant depends only on the dimension when curvature times
radius is bounded. -/
theorem nearby_normalization_volume_ratio {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 1) X) {a : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m + 1) X) (comparisonModelVolume m a))
    {p q : X} {R : ℝ} (hR : 0 < R) (hcurv : a * (3 * R) ≤ 1)
    (hq : q ∈ ball p (R / 4)) :
    (hausdorff (m + 1) X).real (ball p (2 * R)) ≤
      normalizationVolumeRatio m * (hausdorff (m + 1) X).real (ball q (R / 2)) := by
  let μ := hausdorff (m + 1) X
  have hsub : ball p (2 * R) ⊆ ball q (3 * R) := by
    intro x hx
    have hx' := mem_ball.mp hx
    have hq' := mem_ball.mp hq
    have ht := dist_triangle x p q
    rw [dist_comm p q] at ht
    apply mem_ball.mpr
    linarith
  have hvol : μ.real (ball p (2 * R)) ≤ μ.real (ball q (3 * R)) :=
    measureReal_mono hsub (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
  have hsmall := (comparisonModelVolume_bounds m ha (by positivity : 0 ≤ R / 2)).1
  have hbig := (comparisonModelVolume_bounds m ha (by positivity : 0 ≤ 3 * R)).2
  have hcosh : Real.cosh (a * (3 * R)) ≤ Real.cosh 1 := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg ha (by positivity)), abs_of_pos (by norm_num : (0 : ℝ) < 1)]
    exact hcurv
  have hbig' : comparisonModelVolume m a (3 * R) ≤ Real.cosh 1 ^ m * (3 * R) ^ (m + 1) :=
    hbig.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.cosh_pos _).le hcosh m) (by positivity))
  have hc := hBG q (R / 2) (3 * R) (by positivity) (by linarith)
  have hcross : μ.real (ball p (2 * R)) * (R / 2) ^ (m + 1) ≤
      (normalizationVolumeRatio m * μ.real (ball q (R / 2))) * (R / 2) ^ (m + 1) := by
    calc
      _ ≤ μ.real (ball q (3 * R)) * comparisonModelVolume m a (R / 2) :=
        mul_le_mul hvol hsmall (by positivity) measureReal_nonneg
      _ ≤ μ.real (ball q (R / 2)) * comparisonModelVolume m a (3 * R) := hc
      _ ≤ μ.real (ball q (R / 2)) * (Real.cosh 1 ^ m * (3 * R) ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hbig' measureReal_nonneg
      _ = _ := by
        rw [show 3 * R = 6 * (R / 2) by ring, mul_pow]
        dsimp [normalizationVolumeRatio]
        ring
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < (R / 2) ^ (m + 1))).mp hcross

end RegularPointCoordinates

end

end OAI
