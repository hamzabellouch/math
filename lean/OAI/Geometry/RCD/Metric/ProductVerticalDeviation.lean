import OAI.Geometry.RCD.Metric.ProductPackingGrid

namespace OAI

/-! # Horizontal deviation of an almost vertical product geodesic -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates

/-- A small triangle defect between two points of the zero Euclidean fiber
controls the horizontal square. No geodesic structure on the second factor is used. -/
theorem product_vertical_deviation {Z : Type*} [MetricSpace Z] {n : ℕ}
    (w : WithLp 2 (Euclidean n × Z)) (z₀ z₁ : Z) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : dist w (WithLp.toLp 2 (0,z₀))+dist w (WithLp.toLp 2 (0,z₁)) ≤
      dist z₀ z₁+δ) :
    ‖w.fst‖^2 ≤ 2*δ*(dist z₀ z₁+δ) := by
  let A := dist w (WithLp.toLp 2 (0,z₀))
  let B := dist w (WithLp.toLp 2 (0,z₁))
  let a := dist w.snd z₀
  let b := dist w.snd z₁
  have haA : a ≤ A := WithLp.dist_snd_le w (WithLp.toLp 2 (0,z₀))
  have hbB : b ≤ B := WithLp.dist_snd_le w (WithLp.toLp 2 (0,z₁))
  have ha : 0 ≤ a := dist_nonneg
  have hA : 0 ≤ A := dist_nonneg
  have hB : 0 ≤ B := dist_nonneg
  have htri : dist z₀ z₁ ≤ a+b := by
    simpa only [a,b,dist_comm z₀ w.snd] using dist_triangle z₀ w.snd z₁
  have hsq : A^2=‖w.fst‖^2+a^2 := by
    dsimp only [A]
    rw [metric_product_distance_L2,Real.sq_sqrt]
    · simp only [WithLp.fst,WithLp.snd,dist_zero_right,a]
    · positivity
  have hdiff : A-a ≤ δ := by linarith
  have hsum : A+a ≤ 2*(dist z₀ z₁+δ) := by dsimp only [A,B] at *; linarith
  have hmul := mul_le_mul hdiff hsum (by linarith : 0 ≤ A+a) hδ
  nlinarith

end RegularPointCoordinates

end

end OAI
