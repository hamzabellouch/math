import OAI.Geometry.RCD.Sobolev.PhysicalBallMeasuredTests

namespace OAI

/-! # Exact normalization by the smaller physical ball -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem cancel_common_mass {a : ℝ} (ha : a≠0) (b c : ℝ) :
    (a⁻¹*b)/(a⁻¹*c)=c⁻¹*b := by
  rw [div_eq_mul_inv,mul_inv_rev,inv_inv]
  calc a⁻¹*b*(c⁻¹*a) = (a⁻¹*a)*(c⁻¹*b) := by ring
       _ = c⁻¹*b := by rw [inv_mul_cancel₀ ha,one_mul]

theorem inner_ball_measured_test_tendsto {n : ℕ} {S ρ : ℝ}
    (hS : 0<S) (hρ : 0<ρ) (hρS : ρ≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {v : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hv : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (v k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0))
    (φ : Euclidean n →ᵇ ℝ) :
    Tendsto (fun k => (μ.real (ball (p k) (ρ*r k)))⁻¹*
      ∫ x in ball (p k) (ρ*r k), φ (v k x) ∂μ) atTop
      (𝓝 ((volume.real (ball (0:Euclidean n) ρ))⁻¹*(∫ z in ball 0 ρ, φ z))) := by
  have ht := physical_ball_measured_test_tendsto hS hρ hρS hr hv hfin hpos hε φ
  have hm := physical_ball_measured_test_tendsto hS hρ hρS hr hv hfin hpos hε (1 : Euclidean n →ᵇ ℝ)
  change Tendsto (fun k => (μ.real (ball (p k) (S*r k)))⁻¹*
    ∫ _ in ball (p k) (ρ*r k), (1:ℝ) ∂μ) atTop
    (𝓝 ((volume.real (ball (0:Euclidean n) S))⁻¹*(∫ _ in ball (0:Euclidean n) ρ, (1:ℝ)))) at hm
  simp only [setIntegral_const,smul_eq_mul,mul_one] at hm
  have hVS : 0<volume.real (ball (0:Euclidean n) S) := ENNReal.toReal_pos
    (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top
  have hVρ : 0<volume.real (ball (0:Euclidean n) ρ) := ENNReal.toReal_pos
    (measure_ball_pos volume 0 hρ).ne' measure_ball_ne_top
  have hq := ht.div hm (mul_pos (inv_pos.mpr hVS) hVρ).ne'
  rw [cancel_common_mass hVS.ne'] at hq
  exact hq.congr' (Eventually.of_forall fun k => cancel_common_mass (hpos k).ne' _ _)

end RegularPointCoordinates

end

end OAI
