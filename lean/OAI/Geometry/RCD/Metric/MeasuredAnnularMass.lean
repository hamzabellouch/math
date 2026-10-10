import OAI.Geometry.RCD.Sobolev.PhysicalBallMeasuredTests
import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios

namespace OAI

/-! # Measured Euclidean approximation supplies the actual exterior annulus -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem measured_ball_mass_tendsto {n : ℕ} {S R : ℝ} (hS : 0<S) (hR : 0<R) (hRS : R≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*μ.real (ball (p k) (R*r k))) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*volume.real (ball (0:Euclidean n) R))) := by
  have ht := physical_ball_measured_test_tendsto hS hR hRS hr hV hfin hpos hε
    (1 : Euclidean n →ᵇ ℝ)
  simpa only [BoundedContinuousFunction.coe_one,Pi.one_apply,setIntegral_const,smul_eq_mul,mul_one] using ht

theorem measured_annulus_doubles {n : ℕ} (hn : 2≤n) {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : 2*R≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ k in atTop, 2*μ.real (ball (p k) (R*r k))≤μ.real (ball (p k) (2*(R*r k))) := by
  have hi := measured_ball_mass_tendsto hS hR (show R≤S by linarith) hr hV hfin hpos hε
  have ho := measured_ball_mass_tendsto hS (mul_pos (by norm_num) hR) hRS hr hV hfin hpos hε
  have hV0 : 0<volume.real (ball (0:Euclidean n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_ne_top
  have hVS : 0<volume.real (ball (0:Euclidean n) S) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hpow : (4:ℝ)≤2^n := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn
    norm_num at hp ⊢
    exact hp
  have hdiff : 0<(volume.real (ball (0:Euclidean n) S))⁻¹*volume.real (ball (0:Euclidean n) (2*R))-
      2*((volume.real (ball (0:Euclidean n) S))⁻¹*volume.real (ball (0:Euclidean n) R)) := by
    rw [euclidean_ball_real hn0 0 (mul_pos (by norm_num) hR).le,euclidean_ball_real hn0 0 hR.le,mul_pow]
    have hscale : 0<(volume.real (ball (0:Euclidean n) S))⁻¹*R^n*volume.real (ball (0:Euclidean n) 1) :=
      mul_pos (mul_pos (inv_pos.mpr hVS) (pow_pos hR _)) hV0
    nlinarith
  filter_upwards [(ho.sub (hi.const_mul 2)).eventually (Ioi_mem_nhds hdiff)] with k hk
  have hm := inv_pos.mpr (hpos k)
  have he : 2*(R*r k)=(2*R)*r k := by ring
  rw [he]
  nlinarith

end RegularPointCoordinates

end

end OAI
