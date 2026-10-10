import OAI.Geometry.RCD.Metric.BoundedRegionVolume

namespace OAI

/-! # Uniform polynomial normalization volumes on a bounded region -/

open Set MeasureTheory Metric
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.bounded_heat_volume_power {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) (R : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ y, dist y p ≤ R → ∀ t, 0 < t → t ≤ 1 →
      c*(Real.sqrt t)^n ≤ (hausdorff n X).real (ball y (Real.sqrt t)) := by
  obtain ⟨m,hm,hvol⟩ := hX.ball_volume_lower_on_bounded_region hn p R 1 zero_lt_one
  let E := 2*Real.exp (4*Real.sqrt |K|)
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨m/E^n,div_pos hm (pow_pos hE n),?_⟩
  intro y hy t ht ht1
  have hroot : Real.sqrt t ≤ 1 := by nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
  have hk : -|K| ≤ K*(1:ℝ)^2 := by simpa using neg_abs_le K
  have hh := hX.rescaled_ball_volume_lower hn (abs_nonneg K) (Real.sqrt_pos.mpr ht)
    hroot y 1 zero_lt_one hk y (by simp)
  simp only [mul_one] at hh
  calc
    (m/E^n)*(Real.sqrt t)^n = (Real.sqrt t/E)^n*m := by rw [div_pow]; ring
    _ ≤ (Real.sqrt t/E)^n*(hausdorff n X).real (ball y 1) :=
      mul_le_mul_of_nonneg_left (hvol y hy) (by positivity)
    _ ≤ _ := hh

end RegularPointCoordinates

end

end OAI
