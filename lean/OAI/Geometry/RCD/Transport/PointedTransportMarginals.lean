import OAI.Geometry.RCD.Transport.PointedGeodesicInterpolation
import OAI.Geometry.RCD.Sobolev.WeakMapPerturbation
import OAI.Analysis.RCDHeat.DynamicalPlan

namespace OAI

/-! # Affine Euclidean limits of the actual source transport marginals

Once the endpoint-pair laws converge, every fixed intermediate-time law
converges to the affine interpolation of that same limiting pair law.
-/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem pointed_transport_marginals_tendsto {n : ℕ} {S ρ : ℝ}
    (hρ : 0≤ρ) (hroom : 3*ρ≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hm : ∀ k, Measurable (v k)) (P : ℕ → ProbabilityMeasure C(Time,X))
    (hgeo : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), IsGeodesic γ)
    (h0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k)
    (h1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k)
    {Q : ProbabilityMeasure (Euclidean n × Euclidean n)}
    (hpair : Tendsto (fun k => (P k).map (fun γ => (v k (γ 0),v k (γ 1)))) atTop (𝓝 Q))
    (t : Time) :
    Tendsto (fun k => (P k).map (fun γ => v k (γ t))) atTop
      (𝓝 (Q.map (fun xy => (1-(t:ℝ)) • xy.1+(t:ℝ) • xy.2))) := by
  let A : Euclidean n × Euclidean n → Euclidean n :=
    fun xy => (1-(t:ℝ)) • xy.1+(t:ℝ) • xy.2
  have hA : Continuous A := by
    dsimp only [A]
    fun_prop
  let e := fun k (γ : C(Time,X)) => (v k (γ 0),v k (γ 1))
  have he (k : ℕ) : Measurable (e k) :=
    ((hm k).comp (measurable_path_eval 0)).prodMk ((hm k).comp (measurable_path_eval 1))
  have ha := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hpair hA
  change Tendsto (fun k => ((P k).map (e k)).map A) atTop (𝓝 (Q.map A)) at ha
  have heq (k : ℕ) : ((P k).map (e k)).map A=(P k).map (fun γ => A (e k γ)) := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map,Measure.map_map hA.measurable (he k),Function.comp_def]
  have hag : Tendsto (fun k => (P k).map (fun γ => A (e k γ))) atTop (𝓝 (Q.map A)) := by
    simpa only [heq] using ha
  have hd : Tendsto (fun k => Real.sqrt (2*(ε k*(4*ρ+ε k)))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul,Real.sqrt_zero] using
      ((hεlim.mul (hεlim.const_add (4*ρ))).const_mul 2).sqrt
  apply weak_limit_of_map_error P (fun k γ => v k (γ t)) (fun k γ => A (e k γ))
    (fun k => (hm k).comp (measurable_path_eval t)) (fun k => hA.measurable.comp (he k)) hd _ hag
  intro k
  filter_upwards [hgeo k,h0 k,h1 k] with γ hg hg0 hg1
  exact pointed_geodesic_interpolation (hr k) hρ (hε k) hroom (hv k) hg hg0 hg1 t

end RegularPointCoordinates

end

end OAI
