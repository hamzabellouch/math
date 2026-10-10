import OAI.Geometry.RCD.Harmonic.PointedAffineValueLimit
import OAI.Geometry.RCD.Metric.PointedIsometricPerturbation
import OAI.Geometry.RCD.Coordinates.SplittingApproximation

namespace OAI

/-! # Centered maps with an affine isometric limit are pointed approximations -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem pointed_affine_limit_approximation {n : ℕ} (μ : Measure X) [μ.IsOpenPosMeasure]
    (hQ : QuadraticCheegerEnergy μ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) 5 (ε k) (V k))
    (w : Fin n → ℕ → SobolevSpace μ hQ)
    (hv : ∀ k, ContinuousOn (v k) (ball (p k) (5*r k))) (hzero : ∀ k, v k (p k)=0)
    (hrep : ∀ i k, SobolevSpace.toLp μ hQ (w i k) =ᵐ[μ.restrict (ball (p k) (5*r k))]
      fun x => v k x i)
    (g : Fin n → Euclidean n → ℝ) (T : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (haff : ∀ i z, z ∈ ball (0 : Euclidean n) 3 → g i z=g i 0+T z i)
    (hconv : ∀ i W, 0 < W → W < 5 → ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp μ hQ (w i k) x-g i (V k x)| ≤ δ) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
      IsPointedApproximation (p k) 0 (r k) (5/2) τ (v k) := by
  intro τ hτ
  let η := τ/8
  let c : Euclidean n := WithLp.toLp 2 (fun i => g i 0)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hval := pointed_affine_value_limit μ hQ p r ε V v hr hεlim hV w hv hrep g T haff hconv
    (by norm_num : (0:ℝ)<11/4) (by norm_num : (11/4:ℝ)<3) η hη
  filter_upwards [hval,hεlim.eventually (eventually_lt_nhds (show (0:ℝ)<τ/10 by positivity))]
    with k hk hsmall
  have hVp : ‖V k (p k)‖ ≤ ε k := by simpa only [dist_zero_right] using (hV k).1
  have hc0 : ‖c+T (V k (p k))‖ ≤ η := by
    have hh := hk (p k) (mem_ball_self (mul_pos (by norm_num) (hr k)))
    simpa only [hzero k,dist_zero_left] using hh
  have hcnorm : ‖c‖ ≤ η+ε k := by
    have hh := norm_sub_le (c+T (V k (p k))) (T (V k (p k)))
    rw [add_sub_cancel_right,T.norm_map] at hh
    linarith
  have hclose : ∀ x, dist x (p k) ≤ (5/2)*r k →
      dist (v k x) (T (V k x)) ≤ 2*η+ε k := by
    intro x hx
    have hin : x ∈ ball (p k) ((11/4)*r k) := by
      change dist x (p k)<(11/4)*r k
      nlinarith [hr k]
    have hvx := hk x hin
    have hd := dist_triangle (v k x) (c+T (V k x)) (T (V k x))
    have he : dist (c+T (V k x)) (T (V k x))=‖c‖ := by
      rw [dist_eq_norm,add_sub_cancel_right]
    rw [he] at hd
    linarith
  have hp := pointed_isometric_perturbation (hr k) (by norm_num : (0:ℝ)≤5/2)
    (by norm_num : (5/2:ℝ)≤5) (hε k) (by linarith [hε k] : 0≤2*η+ε k)
    (hV k) T (hzero k) hclose
  apply hp.mono_error
  dsimp only [η] at *
  linarith

end RegularPointCoordinates

end

end OAI
