import OAI.Geometry.RCD.Metric.MeasuredDensityPair
import OAI.Geometry.RCD.Transport.BoundedDensityPlanFamily

namespace OAI

/-! # Actual bounded transport families supplied by compact Euclidean densities -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

/-- Bounded source measures, optimal transport plans, compression estimates,
and convergence of their Euclidean pushforwards. -/
structure MeasuredTransportData {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (p : ℕ → X) (r : ℕ → ℝ) (S τ : ℝ) (v : ℕ → X → Euclidean n)
    (α β : ProbabilityMeasure (Euclidean n)) (c₀ : ℝ) where
  offset : ℕ
  left : ℕ → ProbabilityMeasure X
  right : ℕ → ProbabilityMeasure X
  control : ℕ → ℝ
  plan : ℕ → ProbabilityMeasure C(Time,X)
  control_nonneg : ∀ k, 0≤control k
  control_limit : Tendsto control atTop (𝓝 c₀)
  left_bound : ∀ k, (left k : Measure X)≤
    (ENNReal.ofReal (control k)*(hausdorff n X (ball (p (k+offset)) (S*r (k+offset))))⁻¹) • hausdorff n X
  right_bound : ∀ k, (right k : Measure X)≤
    (ENNReal.ofReal (control k)*(hausdorff n X (ball (p (k+offset)) (S*r (k+offset))))⁻¹) • hausdorff n X
  left_support : ∀ k, ∀ᵐ x ∂(left k : Measure X), dist x (p (k+offset))≤τ*r (k+offset)
  right_support : ∀ k, ∀ᵐ x ∂(right k : Measure X), dist x (p (k+offset))≤τ*r (k+offset)
  left_limit : Tendsto (fun k => (left k).map (v (k+offset))) atTop (𝓝 α)
  right_limit : Tendsto (fun k => (right k).map (v (k+offset))) atTop (𝓝 β)
  geodesic : ∀ k, ∀ᵐ γ ∂(plan k : Measure C(Time,X)), IsGeodesic γ
  optimal : ∀ k, IsOptimalCoupling (left k) (right k)
    ((plan k : Measure C(Time,X)).map (fun γ => (γ 0,γ 1)))
  compression : ∀ k t, (plan k : Measure C(Time,X)).map (fun γ => γ t)≤
    compressionBudget K n (2*(τ*r (k+offset)))
      (ENNReal.ofReal (control k)*(hausdorff n X (ball (p (k+offset)) (S*r (k+offset))))⁻¹) • hausdorff n X

theorem NoncollapsedRCD.measured_transport_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S ρ τ : ℝ}
    (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (a b : Euclidean n →ᵇ ℝ) (ha : ∀ z, 0≤a z) (hb : ∀ z, 0≤b z)
    (ha0 : ∀ z, ρ≤‖z‖ → a z=0) (hb0 : ∀ z, ρ≤‖z‖ → b z=0)
    (hapos : 0<∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))
    (hbpos : 0<∫ z, b z ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    Nonempty (MeasuredTransportData hX p r S τ v
      (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n)) (a.integrable _) ha hapos)
      (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n)) (b.integrable _) hb hbpos)
      (max ((∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖a‖)
        ((∫ z, b z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖b‖))) := by
  obtain ⟨N,ν₀,ν₁,c,hc,hcl,hb₀,hb₁,hs₀,hs₁,hw₀,hw₁⟩ :=
    hX.measured_density_pair hS hρτ p r ε v hr hε hv a b ha hb ha0 hb0 hapos hbpos
  let C := fun k => ENNReal.ofReal (c k)*
    (hausdorff n X (ball (p (k+N)) (S*r (k+N))))⁻¹
  have hC (k : ℕ) : C k≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (hX.fullSupport _ _ (mul_pos hS (hr (k+N)))).ne')
  obtain ⟨P,hgeo,hopt,_,hcomp⟩ := hX.bounded_density_plan_family hn
    (fun k => p (k+N)) (fun k => τ*r (k+N)) (fun k => mul_nonneg hτ (hr (k+N)).le)
    ν₀ ν₁ C hC hb₀ hb₁ hs₀ hs₁
  exact ⟨⟨N,ν₀,ν₁,c,P,hc,hcl,hb₀,hb₁,hs₀,hs₁,hw₀,hw₁,hgeo,hopt,hcomp⟩⟩

end RegularPointCoordinates

end

end OAI
