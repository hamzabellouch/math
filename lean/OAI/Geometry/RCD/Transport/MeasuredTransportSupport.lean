import OAI.Geometry.RCD.Transport.MeasuredTransportData
import OAI.Geometry.RCD.Metric.MeasuredDensityPairSupport

namespace OAI

/-! # Actual transport families retain the supports of both source densities -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.measured_transport_data_nonzero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S ρ τ : ℝ}
    (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (a b : Euclidean n →ᵇ ℝ) (ha : ∀ z, 0≤a z) (hb : ∀ z, 0≤b z)
    (ha0 : ∀ z, ρ≤‖z‖ → a z=0) (hb0 : ∀ z, ρ≤‖z‖ → b z=0)
    (hapos : 0<∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))
    (hbpos : 0<∫ z, b z ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    ∃ D : MeasuredTransportData hX p r S τ v
      (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n)) (a.integrable _) ha hapos)
      (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n)) (b.integrable _) hb hbpos)
      (max ((∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖a‖)
        ((∫ z, b z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖b‖)),
      (∀ k, ∀ᵐ x ∂(D.left k : Measure X), a (v (k+D.offset) x)≠0) ∧
      (∀ k, ∀ᵐ x ∂(D.right k : Measure X), b (v (k+D.offset) x)≠0) := by
  obtain ⟨N,ν₀,ν₁,c,hc,hcl,hb₀,hb₁,hs₀,hs₁,hn₀,hn₁,hw₀,hw₁⟩ :=
    hX.measured_density_pair_nonzero hS hρτ p r ε v hr hε hv a b ha hb ha0 hb0 hapos hbpos
  let C := fun k => ENNReal.ofReal (c k)*
    (hausdorff n X (ball (p (k+N)) (S*r (k+N))))⁻¹
  have hC (k : ℕ) : C k≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (hX.fullSupport _ _ (mul_pos hS (hr (k+N)))).ne')
  obtain ⟨P,hgeo,hopt,_,hcomp⟩ := hX.bounded_density_plan_family hn
    (fun k => p (k+N)) (fun k => τ*r (k+N)) (fun k => mul_nonneg hτ (hr (k+N)).le)
    ν₀ ν₁ C hC hb₀ hb₁ hs₀ hs₁
  exact ⟨⟨N,ν₀,ν₁,c,P,hc,hcl,hb₀,hb₁,hs₀,hs₁,hw₀,hw₁,hgeo,hopt,hcomp⟩,hn₀,hn₁⟩


end RegularPointCoordinates

end

end OAI
