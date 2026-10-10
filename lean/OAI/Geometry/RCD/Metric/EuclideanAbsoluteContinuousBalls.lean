import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios

namespace OAI

/-! # Ball identities for an absolutely continuous Euclidean measure -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem absolutelyContinuous_closedBall_eq_ball {n : ℕ} (hn : 0 < n)
    (μ : Measure (Euclidean n)) (hμ : μ ≪ volume) (x : Euclidean n) (r : ℝ) :
    μ (closedBall x r)=μ (ball x r) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hz : μ (sphere x r)=0 := hμ (Measure.addHaar_sphere volume x r)
  apply le_antisymm _ (measure_mono ball_subset_closedBall)
  calc
    _ = μ (ball x r ∪ sphere x r) := congrArg μ ball_union_sphere.symm
    _ ≤ μ (ball x r)+μ (sphere x r) := measure_union_le _ _
    _ = _ := by rw [hz,add_zero]

theorem half_ball_density_le {n : ℕ} (hn : 0 < n)
    (μ : Measure (Euclidean n)) (x y : Euclidean n) {r : ℝ} (hr : 0 < r)
    (hm : (1/2:ℝ)^n*μ.real (closedBall x r) ≤ μ.real (closedBall y (r/2))) :
    μ.real (closedBall x r)/volume.real (closedBall x r) ≤
      μ.real (closedBall y (r/2))/volume.real (closedBall y (r/2)) := by
  have hx : 0 < volume.real (closedBall x r) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne
  have hy : 0 < volume.real (closedBall y (r/2)) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume y (by positivity)).ne' measure_closedBall_lt_top.ne
  have he : volume.real (closedBall y (r/2)) =
      (1/2:ℝ)^n*volume.real (closedBall x r) := by
    rw [euclidean_closedBall_real hn y (by positivity),euclidean_closedBall_real hn x hr.le,
      show r/2=(1/2:ℝ)*r by ring,mul_pow]
    ring
  apply (div_le_div_iff₀ hx hy).mpr
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hm hx.le
  nlinarith only [hh]

end RegularPointCoordinates

end

end OAI
