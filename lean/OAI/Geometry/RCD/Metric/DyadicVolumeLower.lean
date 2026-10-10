import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Dyadic lower volumes at every nearby center -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Iterating one scale-uniform doubling factor gives lower volumes at
all dyadic radii, with the same factor for every nearby center. -/
theorem NoncollapsedRCD.rescaled_dyadic_volume_lower {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ D : ℝ, 2 ≤ D ∧ ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ q : X, dist q p ≤ R → ∀ k : ℕ,
        (hausdorff n X).real (ball p R) ≤
          D^(k+1) * (hausdorff n X).real (ball q (R/2^k)) := by
  obtain ⟨D₀, hD₀, hvol⟩ := hX.rescaled_ball_volume_factor hn
    (a := 1) (δ := 1/2) (by norm_num) (by norm_num) (by norm_num)
  let D := max 2 D₀
  have hD : 2 ≤ D := le_max_left _ _
  have hDD : D₀ ≤ D := le_max_right _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  refine ⟨D, hD, ?_⟩
  intro p R hR hcurv q hq
  have step (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) (y z : X) (hzy : dist z y ≤ r) :
      (hausdorff n X).real (ball y r) ≤
        D * (hausdorff n X).real (ball z (r/2)) := by
    have hc : -1 ≤ K*r^2 := by
      by_cases hK : 0 ≤ K
      · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg r))
      · have hh := mul_le_mul_of_nonpos_left ((sq_le_sq₀ hr.le hR.le).mpr hrR)
          (le_of_not_ge hK)
        linarith
    have hh := hvol y r hr hc z hzy
    have heq : (1/2:ℝ)*r = r/2 := by ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hDD ENNReal.toReal_nonneg)
  intro k
  induction k with
  | zero =>
      have hh := step R hR le_rfl p q hq
      have hmono : (hausdorff n X).real (ball q (R/2)) ≤
          (hausdorff n X).real (ball q R) :=
        measureReal_mono (ball_subset_ball (by linarith : R/2 ≤ R))
          (hX.finiteOnBounded _ isBounded_ball).ne
      simpa only [pow_zero, div_one, zero_add, pow_one] using
        hh.trans (mul_le_mul_of_nonneg_left hmono hDpos.le)
  | succ k ih =>
      have hr : 0 < R/(2:ℝ)^k := div_pos hR (by positivity)
      have hrR : R/(2:ℝ)^k ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
      have hh := step (R/2^k) hr hrR q q (by simp [hr.le])
      have hrad : R/(2:ℝ)^k/2 = R/2^(k+1) := by rw [pow_succ]; ring
      rw [hrad] at hh
      calc
        _ ≤ D^(k+1) * (D * (hausdorff n X).real (ball q (R/2^(k+1)))) :=
          ih.trans (mul_le_mul_of_nonneg_left hh (pow_nonneg hDpos.le _))
        _ = _ := by rw [pow_succ]; ring

end RegularPointCoordinates

end

end OAI
