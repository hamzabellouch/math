import OAI.Geometry.RCD.Sobolev.PointedTestLocalization
import OAI.Geometry.RCD.Sobolev.WeightedEnergyDifference

namespace OAI

/-! # Localized bounded tests of converging densities -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem pointed_weighted_difference_tendsto {n : ℕ} (μ : Measure X)
    {S ρ τ : ℝ} (hS : 0 ≤ S) (hρτ : ρ < τ) (hτS : τ ≤ S)
    (p : ℕ → X) (r ε c : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hc : ∀ k, 0 ≤ c k) (hε : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (V k))
    (hVm : ∀ k, Measurable (V k))
    (f g : ℕ → X → ℝ)
    (hf : ∀ k, IntegrableOn (f k) (ball (p k) (S*r k)) μ)
    (hg : ∀ k, IntegrableOn (g k) (ball (p k) (S*r k)) μ)
    (hlim : Tendsto (fun k => c k*∫ x in ball (p k) (τ*r k), |f k x-g k x| ∂μ)
      atTop (𝓝 0))
    (φ : Euclidean n →ᵇ ℝ) (hs : Function.support φ ⊆ ball 0 ρ) :
    Tendsto (fun k => c k*(∫ x in ball (p k) (S*r k), φ (V k x)*f k x ∂μ)-
      c k*(∫ x in ball (p k) (S*r k), φ (V k x)*g k x ∂μ)) atTop (𝓝 0) := by
  have hsub (k : ℕ) : ball (p k) (τ*r k) ⊆ ball (p k) (S*r k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right hτS (hr k).le)
  have hi := weighted_integral_difference_tendsto μ (fun k => ball (p k) (τ*r k)) c hc
    f g (fun k x => φ (V k x)) (fun k => (hf k).mono_set (hsub k))
    (fun k => (hg k).mono_set (hsub k))
    (fun k => (φ.continuous.measurable.comp (hVm k)).aestronglyMeasurable.restrict)
    (fun k => Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using φ.norm_coe_le_norm (V k x))) hlim
  apply hi.congr'
  filter_upwards [hε.eventually (eventually_lt_nhds
    (show (0:ℝ) < (τ-ρ)/2 by linarith))] with k hk
  have hgap : ρ+2*ε k ≤ τ := by linarith
  exact congrArg₂ (fun a b : ℝ => c k*a-c k*b)
    (pointed_test_integral_localization μ (hr k) hS hgap hτS (hV k) φ hs (f k) measurableSet_ball)
    (pointed_test_integral_localization μ (hr k) hS hgap hτS (hV k) φ hs (g k) measurableSet_ball)

end RegularPointCoordinates

end

end OAI
