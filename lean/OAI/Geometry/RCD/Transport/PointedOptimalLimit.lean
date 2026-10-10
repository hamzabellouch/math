import OAI.Geometry.RCD.Transport.TransportPotentialCompactness
import OAI.Geometry.RCD.Transport.PointedPotentialContact
import OAI.Geometry.RCD.Transport.BoundedCouplingDual

namespace OAI

/-! # Optimality of the actual Euclidean endpoint limit

The proof transfers the original optimal potentials, preserves their exact
contact integral, and tests every coupling of the limiting marginals.
-/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.pointed_optimal_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S ρ : ℝ} (hρ : 0≤ρ) (hρS : ρ<S)
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
    (hs1 : ∀ k, ∀ᵐ x ∂(ν₁ k : Measure X), dist x (p k)≤ρ*r k)
    {Q : ProbabilityMeasure (Euclidean n × Euclidean n)}
    (hpair : Tendsto (fun k => (P k).map (fun γ => (v k (γ 0),v k (γ 1)))) atTop (𝓝 Q))
    (hcost : Tendsto (fun k => ∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r k)^2
      ∂(P k : Measure C(Time,X))) atTop
      (𝓝 (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n))))) :
    IsOptimalCoupling ((Q : Measure (Euclidean n × Euclidean n)).map Prod.fst)
      ((Q : Measure (Euclidean n × Euclidean n)).map Prod.snd) Q := by
  have hend (k : ℕ) := optimalPlan_endpoints (ν₀ k : Measure X) (ν₁ k : Measure X)
    (P k : Measure C(Time,X)) (hp k)
  have h0 (k : ℕ) : ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k :=
    ae_of_ae_map (measurable_path_eval 0).aemeasurable ((hend k).1.symm ▸ hs0 k)
  have h1 (k : ℕ) : ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k :=
    ae_of_ae_map (measurable_path_eval 1).aemeasurable ((hend k).2.symm ▸ hs1 k)
  obtain ⟨φ,ψ,f,g,t,hdata,ht,hf,hg,hφ,hψ,had⟩ := hX.transport_potential_compactness hn
    (hρ.trans hρS.le) hρ p r ε v hr hε hε1 hεlim hv ν₀ ν₁
    (fun k => (P k : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))) hac hp hs0 hs1
  let B := (ρ+S)/2
  have hρB : ρ<B := by dsimp [B]; linarith
  have hBS : B<S := by dsimp [B]; linarith
  have hi (k : ℕ) : Integrable (fun γ : C(Time,X) => φ (t k) (γ 0)+ψ (t k) (γ 1))
      (P (t k) : Measure C(Time,X)) := by
    have hφi : Integrable (fun γ : C(Time,X) => φ (t k) (γ 0))
        (P (t k) : Measure C(Time,X)) :=
      (integrable_const (10*ρ^2)).mono'
        (((hdata (t k)).1.continuous.comp (continuous_eval_const 0)).aestronglyMeasurable)
        (Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using (hdata (t k)).2.2.1 (γ 0))
    have hψi : Integrable (fun γ : C(Time,X) => ψ (t k) (γ 1))
        (P (t k) : Measure C(Time,X)) :=
      (integrable_const (10*ρ^2)).mono'
        (((hdata (t k)).2.1.continuous.comp (continuous_eval_const 1)).aestronglyMeasurable)
        (Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using (hdata (t k)).2.2.2.1 (γ 1))
    exact hφi.add hψi
  have hc (k : ℕ) : ∀ᵐ γ ∂(P (t k) : Measure C(Time,X)),
      φ (t k) (γ 0)+ψ (t k) (γ 1)=(dist (γ 0) (γ 1)/r (t k))^2/2 :=
    ae_of_ae_map ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable
      (hdata (t k)).2.2.2.2.2
  have hcontact := pointed_potential_contact hρ hρB hBS (p ∘ t) (r ∘ t) (ε ∘ t) (v ∘ t)
    (fun k => hr (t k)) (hεlim.comp ht.tendsto_atTop) (fun k => hv (t k))
    (fun k => hm (t k)) (P ∘ t) (fun k => h0 (t k)) (fun k => h1 (t k))
    (hpair.comp ht.tendsto_atTop) (hcost.comp ht.tendsto_atTop)
    (fun k => φ (t k)) (fun k => ψ (t k)) hf hg hi hφ hψ hc
  have hQ := pointed_pair_limit_support hρ hρS.le hρB p r ε v hr hεlim hv hm P h0 h1 hpair
  apply bounded_coupling_optimal_of_dual (hρ.trans hρB.le) Q hQ hf hg _ hcontact
  intro a ha b hb
  apply had a b
  · exact (show ‖a‖≤B by simpa only [mem_closedBall,dist_zero_right] using ha).trans_lt hBS
  · exact (show ‖b‖≤B by simpa only [mem_closedBall,dist_zero_right] using hb).trans_lt hBS

end RegularPointCoordinates

end

end OAI
