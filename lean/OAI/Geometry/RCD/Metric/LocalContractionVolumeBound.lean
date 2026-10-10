import OAI.Geometry.RCD.Metric.BallMassFubini
import OAI.Geometry.RCD.Metric.MetricLimitLocalContraction

namespace OAI

/-! # A local upper ball-mass bound from the sharp midpoint contraction -/

open Set Metric Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_contraction_volume_bound {n : ℕ}
    (Q : ProbabilityMeasure (Euclidean n)) (z : Euclidean n) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ x ∈ ball z δ, ∀ y ∈ ball z δ, ∀ b : ℝ, 0 < b → b ≤ δ →
      (1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball y b) ≤
        (Q : Measure (Euclidean n)).real (closedBall ((1/2:ℝ) • (x+y)) (b/2)))
    {y : Euclidean n} (hy : y ∈ ball z (δ/4)) {b : ℝ} (hb : 0 < b) (hbδ : b ≤ δ) :
    ((1/2:ℝ)^n*(Q : Measure (Euclidean n)).real (ball y b))*
      volume.real (ball z (δ/4)) ≤ volume.real (closedBall (0 : Euclidean n) (b/2)) := by
  let μ := (Q : Measure (Euclidean n))
  let D := ball z (δ/4)
  let c := (1/2:ℝ)^n*μ.real (ball y b)
  have hc0 : 0 ≤ c := mul_nonneg (pow_nonneg (by norm_num) n) measureReal_nonneg
  have hlocal (w : Euclidean n) (hw : w ∈ D) : c ≤ μ.real (closedBall w (b/2)) := by
    let x := w+(w-y)
    have hxw : dist x w = dist w y := by simp [x,dist_eq_norm]
    have hdx : dist x z ≤ 2*dist w z+dist y z := by
      have h1 := dist_triangle x w z
      have h2 := dist_triangle w z y
      rw [dist_comm z y] at h2
      rw [hxw] at h1
      linarith
    have hx : x ∈ ball z δ := by
      have hw' : dist w z < δ/4 := hw
      have hy' : dist y z < δ/4 := hy
      change dist x z < δ
      linarith
    have hyδ : y ∈ ball z δ := (ball_subset_ball (by linarith)) hy
    have hm : (1/2:ℝ) • (x+y)=w := by dsimp only [x]; module
    simpa only [hm] using hc x hx y hyδ b hb hbδ
  have henn (w : Euclidean n) (hw : w ∈ D) :
      ENNReal.ofReal c ≤ μ (closedBall w (b/2)) := by
    have hh := ENNReal.ofReal_le_ofReal (hlocal w hw)
    simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top μ _)] using hh
  have hi : ENNReal.ofReal c*volume D ≤ ∫⁻ w in D, μ (closedBall w (b/2)) := by
    calc
      _ = ∫⁻ _w in D, ENNReal.ofReal c := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet D)] with w hw
        exact henn w hw
  have hglobal : (∫⁻ w in D, μ (closedBall w (b/2))) ≤
      volume (closedBall (0 : Euclidean n) (b/2)) := by
    calc
      _ ≤ ∫⁻ w, μ (closedBall w (b/2)) := setLIntegral_le_lintegral _ _
      _ = volume (closedBall (0 : Euclidean n) (b/2))*μ univ := lintegral_closedBall_mass μ _
      _ = _ := by simp [μ]
  have hr := ENNReal.toReal_mono measure_closedBall_lt_top.ne (hi.trans hglobal)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc0] at hr
  simpa only [c,D,μ,Measure.real] using hr

end RegularPointCoordinates

end

end OAI
