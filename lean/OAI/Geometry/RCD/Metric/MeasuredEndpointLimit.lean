import OAI.Geometry.RCD.Transport.MeasuredTransportData
import OAI.Geometry.RCD.Transport.PointedOptimalEndpointCompactness
import OAI.Geometry.RCD.Transport.PlanLimitMarginals

namespace OAI

/-! # Optimal endpoint limits of interior density transports -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem MeasuredTransportData.extract_endpoint_limit {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hn : 2≤n) {p : ℕ → X} {r ε : ℕ → ℝ} {S τ : ℝ} {v : ℕ → X → Euclidean n}
    {α β : ProbabilityMeasure (Euclidean n)} {c₀ : ℝ}
    (D : MeasuredTransportData hX p r S τ v α β c₀)
    (hS : 0<S) (hτ : 0≤τ) (hτS : τ<S)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k)) :
    ∃ Q : ProbabilityMeasure (Euclidean n × Euclidean n), ∃ t : ℕ → ℕ,
      StrictMono t ∧ IsOptimalCoupling (α : Measure (Euclidean n))
        (β : Measure (Euclidean n)) (Q : Measure (Euclidean n × Euclidean n)) ∧
      Tendsto (fun k => (D.plan (t k)).map
        (fun γ => (v (t k+D.offset) (γ 0),v (t k+D.offset) (γ 1)))) atTop (𝓝 Q) ∧
      Tendsto (fun k => ∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r (t k+D.offset))^2
        ∂(D.plan (t k) : Measure C(Time,X))) atTop
        (𝓝 (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))) := by
  have hac (k : ℕ) : (D.left k : Measure X) ≪ hausdorff n X :=
    Measure.absolutelyContinuous_of_le_smul (D.left_bound k)
  obtain ⟨Q,t,ht,hopt,hpair,hcost⟩ := hX.pointed_optimal_endpoint_subsequence hn hS hτ hτS
    (fun k => p (k+D.offset)) (fun k => r (k+D.offset))
    (fun k => ε (k+D.offset)) (fun k => v (k+D.offset))
    (fun k => hr (k+D.offset)) (fun k => hε (k+D.offset)) (fun k => hε1 (k+D.offset))
    (hεlim.comp (tendsto_add_atTop_nat D.offset))
    (fun k => (hv (k+D.offset)).metric) (fun k => (hv (k+D.offset)).measurable)
    D.plan D.left D.right hac D.optimal D.left_support D.right_support
  have hend (k : ℕ) := optimalPlan_endpoints (D.left k : Measure X) (D.right k : Measure X)
    (D.plan k : Measure C(Time,X)) (D.optimal k)
  have hends := mapped_plan_limit_marginals (D.plan ∘ t) (fun k => v (t k+D.offset))
    (fun k => (hv (t k+D.offset)).measurable) (D.left ∘ t) (D.right ∘ t)
    (fun k => (hend (t k)).1) (fun k => (hend (t k)).2) hpair
    (D.left_limit.comp ht.tendsto_atTop) (D.right_limit.comp ht.tendsto_atTop)
  rw [hends.1,hends.2] at hopt
  exact ⟨Q,t,ht,hopt,hpair,hcost⟩

end RegularPointCoordinates

end

end OAI
