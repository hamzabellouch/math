import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # A uniform volume comparison between a heat time and its half -/

open Set MeasureTheory Metric

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The single scale comparison needed when splitting the heat semigroup. -/
theorem NoncollapsedRCD.heat_half_volume_comparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ z : X,
      (hausdorff n X).real (ball z (Real.sqrt t)) ≤
        D*(hausdorff n X).real (ball z (Real.sqrt (t/2))) := by
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (abs_nonneg K)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
  refine ⟨D,hD,?_⟩
  intro t ht ht1 z
  have hcurv : -|K| ≤ K*(Real.sqrt t)^2 := by
    rw [Real.sq_sqrt ht.le]
    have h1 := mul_nonneg (by linarith [neg_abs_le K] : 0 ≤ K+|K|) ht.le
    have h2 := mul_nonneg (abs_nonneg K) (sub_nonneg.mpr ht1)
    nlinarith
  have hh := hvol z (Real.sqrt t) (Real.sqrt_pos.mpr ht) hcurv z (by simp)
  have hrad : (1/2:ℝ)*Real.sqrt t ≤ Real.sqrt (t/2) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow,Real.sq_sqrt ht.le]
    nlinarith
  have hm := measureReal_mono (Metric.ball_subset_ball hrad)
    (hX.finiteOnBounded (ball z (Real.sqrt (t/2))) isBounded_ball).ne
  exact hh.trans (mul_le_mul_of_nonneg_left hm (by linarith))

end RegularPointCoordinates

end

end OAI
