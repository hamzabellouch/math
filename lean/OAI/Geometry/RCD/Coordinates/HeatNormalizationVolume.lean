import OAI.Geometry.RCD.Heat.HeatGaussianRadius
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Volume factors at the Gaussian localization scale

These estimates use the actual CD volume comparison already proved for
the space. There is no model-volume or Gaussian premise.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)

include hX hn

theorem NoncollapsedRCD.ball_volume_ratio_exp (p q : X) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hq : dist q p ≤ R) :
    (hausdorff n X).real (ball p R) ≤
      (2*R/r*Real.exp (4*Real.sqrt |K| *R))^n*(hausdorff n X).real (ball q r) := by
  have hR : 0 < R := hr.trans_le hrR
  have ha : 0 ≤ |K| *R^2 := mul_nonneg (abs_nonneg K) (sq_nonneg R)
  have hcurv : -(|K| *R^2) ≤ K*R^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg R)]
  have hb := hX.rescaled_ball_volume_lower hn ha (div_pos hr hR)
    ((div_le_one hR).mpr hrR) p R hR hcurv q hq
  have hsqrt : Real.sqrt (|K| *R^2) = Real.sqrt |K| *R := by
    rw [Real.sqrt_mul (abs_nonneg K),Real.sqrt_sq hR.le]
  rw [hsqrt,div_mul_cancel₀ r hR.ne'] at hb
  let a := 2*R/r*Real.exp (4*Real.sqrt |K| *R)
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have he : a*((r/R)/(2*Real.exp (4*(Real.sqrt |K| *R)))) = 1 := by
    dsimp only [a]
    rw [show 4*(Real.sqrt |K| *R) = 4*Real.sqrt |K| *R by ring]
    field_simp
  have hh := mul_le_mul_of_nonneg_left hb (pow_nonneg ha0 n)
  rw [← mul_assoc,← mul_pow,he,one_pow,one_mul] at hh
  exact hh

theorem NoncollapsedRCD.gaussian_normalization_volume (y q : X) {t d : ℝ}
    (ht : 0 < t) (hd : 0 ≤ d) (hq : dist q y ≤ d) :
    (hausdorff n X).real (ball y (Real.sqrt t)) ≤
      (4^n*Real.exp ((n:ℝ)*(d/Real.sqrt t)+5*(n:ℝ)*Real.sqrt (|K| *t)+
        4*(n:ℝ)*Real.sqrt |K| *d)) *
        (hausdorff n X).real (ball q (gaussianRadius K t)) := by
  let T := Real.sqrt t
  let u := Real.sqrt (|K| *t)
  let R := T+d
  let r := gaussianRadius K t
  have hT : 0 < T := Real.sqrt_pos.mpr ht
  have hr : 0 < r := gaussianRadius_pos K ht
  have hrR : r ≤ R := (gaussianRadius_le K ht).trans (by dsimp only [R,T]; linarith [Real.sqrt_nonneg t])
  have hqR : dist q y ≤ R := hq.trans (by dsimp only [R]; linarith)
  have hh := hX.ball_volume_ratio_exp hn y q hr hrR hqR
  have hV : (hausdorff n X).real (ball y T) ≤ (hausdorff n X).real (ball y R) :=
    measureReal_mono (ball_subset_ball (by dsimp only [R]; linarith))
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hbase : 2*R/r*Real.exp (4*Real.sqrt |K| *R) ≤
      4*Real.exp (d/T+5*u+4*Real.sqrt |K| *d) := by
    have he : 2*R/r = 4*(1+d/T)*(1+u) := by
      dsimp only [R,r,gaussianRadius,T,u]
      field_simp
      ring
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hdt : 0 ≤ d/T := div_nonneg hd hT.le
    have h1 : 1+d/T ≤ Real.exp (d/T) := by linarith only [Real.add_one_le_exp (d/T)]
    have h2 : 1+u ≤ Real.exp u := by linarith only [Real.add_one_le_exp u]
    have hs : Real.sqrt |K| *T = u := by
      dsimp only [T,u]
      rw [Real.sqrt_mul (abs_nonneg K)]
    rw [he]
    calc
      _ ≤ (4*(Real.exp (d/T)*Real.exp u))*Real.exp (4*Real.sqrt |K| *R) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le)
            (by norm_num : (0:ℝ) ≤ 4)) (Real.exp_pos (4*Real.sqrt |K| *R)).le
      _ = _ := by
        rw [mul_assoc (4:ℝ),← Real.exp_add,← Real.exp_add]
        congr 2
        dsimp only [R]
        nlinarith only [hs]
  have hcoef := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*R/r*Real.exp (4*Real.sqrt |K| *R)) hbase n
  have he : (4*Real.exp (d/T+5*u+4*Real.sqrt |K| *d))^n =
      4^n*Real.exp ((n:ℝ)*(d/T)+5*(n:ℝ)*u+4*(n:ℝ)*Real.sqrt |K| *d) := by
    rw [mul_pow,← Real.exp_nat_mul]
    congr 2
    ring
  rw [he] at hcoef
  exact hV.trans (hh.trans (mul_le_mul_of_nonneg_right hcoef ENNReal.toReal_nonneg))

end RegularPointCoordinates

end

end OAI
