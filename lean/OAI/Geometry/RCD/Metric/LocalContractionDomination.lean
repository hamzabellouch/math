import OAI.Geometry.RCD.Metric.LocalContractionVolumeBound
import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios

namespace OAI

/-! # Domination of small balls by a fixed multiple of Euclidean volume -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem local_contraction_ball_domination {n : ℕ} (hn : 0 < n)
    (Q : ProbabilityMeasure (Euclidean n)) (z : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ x ∈ ball z δ, ∀ y ∈ ball z δ, ∀ b : ℝ, 0 < b → b ≤ δ →
      (1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball y b) ≤
        (Q : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (x+y)) (b/2)))
    {y : Euclidean n} (hy : y ∈ ball z (δ/4)) {b : ℝ} (hb : 0 < b) (hbδ : b ≤ δ) :
    (Q : Measure (Euclidean n)).real (ball y b) ≤
      (volume.real (ball z (δ/4)))⁻¹*volume.real (ball y b) := by
  have h := local_contraction_volume_bound Q z hδ hc hy hb hbδ
  have he : volume.real (closedBall (0 : Euclidean n) (b/2)) =
      (1/2:ℝ)^n*volume.real (ball y b) := by
    rw [euclidean_closedBall_real hn _ (by positivity),euclidean_ball_real hn _ hb.le]
    rw [show b/2=(1/2:ℝ)*b by ring,mul_pow]
    ring
  rw [he] at h
  have hhalf : 0 < (1/2:ℝ)^n := pow_pos (by norm_num) n
  have hcancel : (Q : Measure (Euclidean n)).real (ball y b)*volume.real (ball z (δ/4)) ≤
      volume.real (ball y b) := by
    apply (mul_le_mul_iff_right₀ hhalf).mp
    simpa only [mul_assoc] using h
  have hvol : 0 < volume.real (ball z (δ/4)) :=
    ENNReal.toReal_pos (measure_ball_pos volume z (by positivity)).ne' measure_ball_lt_top.ne
  have hdiv := (le_div_iff₀ hvol).mpr hcancel
  simpa only [div_eq_mul_inv,mul_comm] using hdiv

end RegularPointCoordinates

end

end OAI
