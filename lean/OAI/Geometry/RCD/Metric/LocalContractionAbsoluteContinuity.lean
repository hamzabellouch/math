import OAI.Geometry.RCD.Metric.LocalContractionDomination
import OAI.Geometry.RCD.Metric.LocalBallMeasureOrder

namespace OAI

/-! # Local absolute continuity of a measure with sharp midpoint contraction -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_contraction_absolutelyContinuous {n : ℕ} (hn : 0 < n)
    (Q : ProbabilityMeasure (Euclidean n)) (z : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ x ∈ ball z δ, ∀ y ∈ ball z δ, ∀ b : ℝ, 0 < b → b ≤ δ →
      (1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball y b) ≤
        (Q : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (x+y)) (b/2))) :
    (Q : Measure (Euclidean n)).restrict (ball z (δ/4)) ≪ volume := by
  let c : ℝ≥0 := ⟨(volume.real (ball z (δ/4)))⁻¹*2^n,by positivity⟩
  apply local_ball_absolutelyContinuous (Q : Measure (Euclidean n)) c
    measurableSet_ball (show 0 < δ/2 by positivity)
  intro y hy r hr hrδ
  have hopen := local_contraction_ball_domination hn Q z hδ hc hy
    (show 0 < 2*r by positivity) (show 2*r ≤ δ by linarith)
  have hv : volume.real (ball y (2*r)) = 2^n*volume.real (closedBall y r) := by
    rw [euclidean_ball_real hn y (by positivity),euclidean_closedBall_real hn y hr.le,mul_pow]
    ring
  rw [hv] at hopen
  have hmono := measureReal_mono (closedBall_subset_ball (show r < 2*r by linarith))
    (measure_ne_top (Q : Measure (Euclidean n)) (ball y (2*r)))
  have hreal : (Q : Measure (Euclidean n)).real (closedBall y r) ≤
      (c:ℝ)*volume.real (closedBall y r) := by
    apply hmono.trans
    change (Q : Measure (Euclidean n)).real (ball y (2*r)) ≤
      ((volume.real (ball z (δ/4)))⁻¹*2^n)*volume.real (closedBall y r)
    simpa only [mul_assoc] using hopen
  apply (ENNReal.toReal_le_toReal (measure_ne_top (Q : Measure (Euclidean n)) _)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_closedBall_lt_top (μ := volume)).ne)).mp
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,Measure.real] using hreal

end RegularPointCoordinates

end

end OAI
