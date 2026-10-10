import OAI.Geometry.RCD.Transport.PointedTransportMarginals
import OAI.Geometry.RCD.Metric.EuclideanPairCompactness
import OAI.Geometry.RCD.Transport.PointedPlanCost

namespace OAI

/-! # Endpoint compactness on any strict interior physical ball -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem pointed_endpoint_plan_subsequence {n : ℕ} {S ρ : ℝ}
    (hρ : 0≤ρ) (hρS : ρ≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hm : ∀ k, Measurable (v k)) (P : ℕ → ProbabilityMeasure C(Time,X))
    (h0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k)
    (h1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k) :
    ∃ Q : ProbabilityMeasure (Euclidean n × Euclidean n), ∃ t : ℕ → ℕ,
      StrictMono t ∧
      Tendsto (fun k => (P (t k)).map (fun γ => (v (t k) (γ 0),v (t k) (γ 1)))) atTop (𝓝 Q) ∧
      Tendsto (fun k => ∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r (t k))^2
        ∂(P (t k) : Measure C(Time,X))) atTop
        (𝓝 (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))) := by
  let e := fun k (γ : C(Time,X)) => (v k (γ 0),v k (γ 1))
  have he (k : ℕ) : Measurable (e k) :=
    ((hm k).comp (measurable_path_eval 0)).prodMk ((hm k).comp (measurable_path_eval 1))
  have hS : 0≤S := hρ.trans hρS
  have hb (k : ℕ) : ∀ᵐ xy ∂((P k).map (e k) : Measure (Euclidean n × Euclidean n)),
      xy∈closedBall (0:Euclidean n) (ρ+2) ×ˢ closedBall (0:Euclidean n) (ρ+2) := by
    rw [ProbabilityMeasure.toMeasure_map]
    apply (ae_map_iff (he k).aemeasurable (measurableSet_closedBall.prod measurableSet_closedBall)).mpr
    filter_upwards [h0 k,h1 k] with γ hg0 hg1
    have hnorm (j : Time) (hj : dist (γ j) (p k)≤ρ*r k) : ‖v k (γ j)‖≤ρ+2 := by
      have hrad := (abs_le.mp (pointed_radial_distance (hr k) hS (hv k)
        (hj.trans (mul_le_mul_of_nonneg_right hρS (hr k).le)))).2
      have hd := (div_le_iff₀ (hr k)).mpr hj
      linarith [hε1 k]
    exact ⟨by simpa only [mem_closedBall,dist_zero_right] using hnorm 0 hg0,
      by simpa only [mem_closedBall,dist_zero_right] using hnorm 1 hg1⟩
  obtain ⟨Q,t,ht,hpair,hQ⟩ := euclidean_pair_subsequence (fun k => (P k).map (e k)) (ρ+2) hb
  refine ⟨Q,t,ht,hpair,?_⟩
  exact pointed_plan_cost_tendsto hρ hρS (by linarith : 0≤ρ+2)
      (p ∘ t) (r ∘ t) (ε ∘ t) (v ∘ t)
      (fun k => hr (t k)) (fun k => hε (t k)) (hεlim.comp ht.tendsto_atTop)
      (fun k => hv (t k)) (fun k => hm (t k)) (P ∘ t)
      (fun k => h0 (t k)) (fun k => h1 (t k)) hpair (fun k => hb (t k)) hQ

end RegularPointCoordinates

end

end OAI
