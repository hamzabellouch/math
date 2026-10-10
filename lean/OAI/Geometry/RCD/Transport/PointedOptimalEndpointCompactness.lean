import OAI.Geometry.RCD.Transport.PointedOptimalLimit
import OAI.Geometry.RCD.Metric.PointedEndpointCompactness

namespace OAI

/-! # Optimal endpoint limits on every strict interior physical ball -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.pointed_optimal_endpoint_subsequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S ρ : ℝ}
    (_hS : 0<S) (hρ : 0≤ρ) (hρS : ρ<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hm : ∀ k, Measurable (v k)) (P : ℕ → ProbabilityMeasure C(Time,X))
    (ν₀ ν₁ : ℕ → ProbabilityMeasure X)
    (hac : ∀ k, (ν₀ k : Measure X) ≪ hausdorff n X)
    (hp : ∀ k, IsOptimalCoupling (ν₀ k) (ν₁ k)
      ((P k : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))))
    (hs0 : ∀ k, ∀ᵐ x ∂(ν₀ k : Measure X), dist x (p k)≤ρ*r k)
    (hs1 : ∀ k, ∀ᵐ x ∂(ν₁ k : Measure X), dist x (p k)≤ρ*r k) :
    ∃ Q : ProbabilityMeasure (Euclidean n × Euclidean n), ∃ t : ℕ → ℕ,
      StrictMono t ∧
      IsOptimalCoupling ((Q : Measure (Euclidean n × Euclidean n)).map Prod.fst)
        ((Q : Measure (Euclidean n × Euclidean n)).map Prod.snd) Q ∧
      Tendsto (fun k => (P (t k)).map (fun γ => (v (t k) (γ 0),v (t k) (γ 1)))) atTop (𝓝 Q) ∧
      Tendsto (fun k => ∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r (t k))^2
        ∂(P (t k) : Measure C(Time,X))) atTop
        (𝓝 (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))) := by
  have hend (k : ℕ) := optimalPlan_endpoints (ν₀ k : Measure X) (ν₁ k : Measure X)
    (P k : Measure C(Time,X)) (hp k)
  have h0 (k : ℕ) : ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k :=
    ae_of_ae_map (measurable_path_eval 0).aemeasurable ((hend k).1.symm ▸ hs0 k)
  have h1 (k : ℕ) : ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k :=
    ae_of_ae_map (measurable_path_eval 1).aemeasurable ((hend k).2.symm ▸ hs1 k)
  obtain ⟨Q,t,ht,hpair,hcost⟩ := pointed_endpoint_plan_subsequence hρ hρS.le p r ε v hr hε hε1
    hεlim hv hm P h0 h1
  refine ⟨Q,t,ht,?_,hpair,hcost⟩
  exact hX.pointed_optimal_limit hn hρ hρS (p ∘ t) (r ∘ t) (ε ∘ t) (v ∘ t)
    (fun k => hr (t k)) (fun k => hε (t k)) (fun k => hε1 (t k))
    (hεlim.comp ht.tendsto_atTop) (fun k => hv (t k)) (fun k => hm (t k)) (P ∘ t)
    (ν₀ ∘ t) (ν₁ ∘ t) (fun k => hac (t k)) (fun k => hp (t k))
    (fun k => hs0 (t k)) (fun k => hs1 (t k)) hpair hcost

end RegularPointCoordinates

end

end OAI
