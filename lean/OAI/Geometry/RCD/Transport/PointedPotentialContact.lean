import OAI.Geometry.RCD.Transport.PointedPlanSupport
import OAI.Geometry.RCD.Sobolev.WeakMapUniformIntegrals
import OAI.Geometry.RCD.Sobolev.BoundedLocalRepresentative

namespace OAI

/-! # The exact contact integral for the limiting Euclidean potentials -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem pointed_potential_contact {n : ℕ} {S ρ B : ℝ}
    (hρ : 0≤ρ) (hρB : ρ<B) (hBS : B<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hm : ∀ k, Measurable (v k)) (P : ℕ → ProbabilityMeasure C(Time,X))
    (h0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k)
    (h1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k)
    {Q : ProbabilityMeasure (Euclidean n × Euclidean n)}
    (hpair : Tendsto (fun k => (P k).map (fun γ => (v k (γ 0),v k (γ 1)))) atTop (𝓝 Q))
    (hcost : Tendsto (fun k => ∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r k)^2
      ∂(P k : Measure C(Time,X))) atTop
      (𝓝 (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))))
    (φ ψ : ℕ → X → ℝ) {f g : Euclidean n → ℝ} {L M : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith M g)
    (hi : ∀ k, Integrable (fun γ : C(Time,X) => φ k (γ 0)+ψ k (γ 1))
      (P k : Measure C(Time,X)))
    (hφ : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
      dist x (p k)≤S*r k → |φ k x-f (v k x)|<δ)
    (hψ : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
      dist x (p k)≤S*r k → |ψ k x-g (v k x)|<δ)
    (hc : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)),
      φ k (γ 0)+ψ k (γ 1)=(dist (γ 0) (γ 1)/r k)^2/2) :
    (∫ z, f z.1+g z.2 ∂(Q : Measure (Euclidean n × Euclidean n)))=
      (∫ z, dist z.1 z.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))/2 := by
  have hρS : ρ≤S := hρB.le.trans hBS.le
  have hB : 0≤B := hρ.trans hρB.le
  obtain ⟨F,hF⟩ := bounded_local_representative hB hf.lipschitzOnWith
  obtain ⟨G,hG⟩ := bounded_local_representative hB hg.lipschitzOnWith
  let H : (Euclidean n × Euclidean n) →ᵇ ℝ :=
    F.compContinuous ⟨Prod.fst,continuous_fst⟩+G.compContinuous ⟨Prod.snd,continuous_snd⟩
  have himage : ∀ᶠ k in atTop, ∀ x, dist x (p k)≤ρ*r k → v k x∈closedBall 0 B := by
    filter_upwards [hεlim.eventually (Iio_mem_nhds (half_pos (sub_pos.mpr hρB)))] with k hk x hx
    have ha := (abs_le.mp (pointed_radial_distance (hr k) (hρ.trans hρS) (hv k)
      (hx.trans (mul_le_mul_of_nonneg_right hρS (hr k).le)))).2
    have hd := (div_le_iff₀ (hr k)).mpr hx
    rw [mem_closedBall,dist_zero_right]
    linarith
  have herr : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ γ ∂(P k : Measure C(Time,X)),
      |(φ k (γ 0)+ψ k (γ 1))-H (v k (γ 0),v k (γ 1))|≤δ := by
    intro δ hδ
    filter_upwards [himage,hφ (δ/2) (half_pos hδ),hψ (δ/2) (half_pos hδ)] with k hk hf' hg'
    filter_upwards [h0 k,h1 k] with γ hγ0 hγ1
    change |(φ k (γ 0)+ψ k (γ 1))-(F (v k (γ 0))+G (v k (γ 1)))|≤δ
    rw [hF (hk _ hγ0),hG (hk _ hγ1)]
    have hp0 := hf' (γ 0) (hγ0.trans (mul_le_mul_of_nonneg_right hρS (hr k).le))
    have hp1 := hg' (γ 1) (hγ1.trans (mul_le_mul_of_nonneg_right hρS (hr k).le))
    have hh := abs_add_le (φ k (γ 0)-f (v k (γ 0))) (ψ k (γ 1)-g (v k (γ 1)))
    have heq : φ k (γ 0)-f (v k (γ 0))+(ψ k (γ 1)-g (v k (γ 1)))=
      φ k (γ 0)+ψ k (γ 1)-(f (v k (γ 0))+g (v k (γ 1))) := by ring
    rw [heq] at hh
    linarith
  have ht := weak_map_uniform_integrals P (fun k γ => (v k (γ 0),v k (γ 1)))
    (fun k => ((hm k).comp (measurable_path_eval 0)).prodMk
      ((hm k).comp (measurable_path_eval 1))) hpair
    (fun k γ => φ k (γ 0)+ψ k (γ 1)) hi H herr
  have heq (k : ℕ) :
      (∫ γ : C(Time,X), φ k (γ 0)+ψ k (γ 1) ∂(P k : Measure C(Time,X)))=
      (∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r k)^2 ∂(P k : Measure C(Time,X)))/2 := by
    rw [integral_congr_ae (hc k),integral_div]
  simp_rw [heq] at ht
  have he := tendsto_nhds_unique ht (hcost.div_const 2)
  have hQ := pointed_pair_limit_support hρ hρS hρB p r ε v hr hεlim hv hm P h0 h1 hpair
  have hH : (∫ z, H z ∂(Q : Measure (Euclidean n × Euclidean n)))=
      ∫ z, f z.1+g z.2 ∂(Q : Measure (Euclidean n × Euclidean n)) := by
    apply integral_congr_ae
    filter_upwards [hQ] with z hz
    exact congrArg₂ (·+·) (hF hz.1) (hG hz.2)
  rwa [hH] at he

end RegularPointCoordinates

end

end OAI
