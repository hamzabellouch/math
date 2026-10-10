import OAI.Geometry.RCD.Transport.PointedPlanCompactness

namespace OAI

/-! # Interior support of the limiting endpoint law -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

 theorem weak_limit_ae_closed {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (νs : ℕ → ProbabilityMeasure Y) {ν : ProbabilityMeasure Y}
    (hlim : Tendsto νs atTop (𝓝 ν)) {A : Set Y} (hA : IsClosed A)
    (hs : ∀ᶠ k in atTop, ∀ᵐ z ∂(νs k : Measure Y), z∈A) :
    ∀ᵐ z ∂(ν : Measure Y), z∈A := by
  apply ae_iff.mpr
  change (ν : Measure Y) Aᶜ=0
  have hz : ∀ᶠ k in atTop, (νs k : Measure Y) Aᶜ=0 := hs.mono (fun _ hk => ae_iff.mp hk)
  have hh := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA.isOpen_compl
  simpa only [liminf_congr hz,liminf_const,le_zero_iff] using hh

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem pointed_pair_limit_support {n : ℕ} {S ρ B : ℝ}
    (hρ : 0≤ρ) (hρS : ρ≤S) (hρB : ρ<B)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hm : ∀ k, Measurable (v k)) (P : ℕ → ProbabilityMeasure C(Time,X))
    (h0 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 0) (p k)≤ρ*r k)
    (h1 : ∀ k, ∀ᵐ γ ∂(P k : Measure C(Time,X)), dist (γ 1) (p k)≤ρ*r k)
    {Q : ProbabilityMeasure (Euclidean n × Euclidean n)}
    (hpair : Tendsto (fun k => (P k).map (fun γ => (v k (γ 0),v k (γ 1)))) atTop (𝓝 Q)) :
    ∀ᵐ z ∂(Q : Measure (Euclidean n × Euclidean n)),
      z∈closedBall (0:Euclidean n) B ×ˢ closedBall (0:Euclidean n) B := by
  apply weak_limit_ae_closed _ hpair (isClosed_closedBall.prod isClosed_closedBall)
  filter_upwards [hεlim.eventually (Iio_mem_nhds (half_pos (sub_pos.mpr hρB)))] with k hk
  rw [ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (((hm k).comp (measurable_path_eval 0)).prodMk
    ((hm k).comp (measurable_path_eval 1))).aemeasurable
    (measurableSet_closedBall.prod measurableSet_closedBall)).mpr
  filter_upwards [h0 k,h1 k] with γ hg0 hg1
  have hb (j : Time) (hj : dist (γ j) (p k)≤ρ*r k) : v k (γ j)∈closedBall 0 B := by
    have ha := (abs_le.mp (pointed_radial_distance (hr k) (hρ.trans hρS) (hv k)
      (hj.trans (mul_le_mul_of_nonneg_right hρS (hr k).le)))).2
    have hd := (div_le_iff₀ (hr k)).mpr hj
    rw [mem_closedBall,dist_zero_right]
    linarith
  exact ⟨hb 0 hg0,hb 1 hg1⟩

end RegularPointCoordinates

end

end OAI
