import OAI.Geometry.RCD.Transport.PointedPlanSupport
import OAI.Geometry.RCD.Sobolev.BoundedLocalRepresentative
import OAI.Geometry.RCD.Sobolev.WeakMapUniformIntegrals

namespace OAI

/-! # Local value integrals under the actual bounded source laws -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem pointed_measure_image_support {n : ℕ} {S ρ B : ℝ}
    (hρ : 0≤ρ) (hρS : ρ≤S) (hρB : ρ<B)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (σ : ℕ → ProbabilityMeasure X)
    (hs : ∀ k, ∀ᵐ x ∂(σ k : Measure X), dist x (p k)≤ρ*r k) :
    ∀ᶠ k in atTop, ∀ᵐ x ∂(σ k : Measure X), v k x∈closedBall (0:Euclidean n) B := by
  filter_upwards [hεlim.eventually (Iio_mem_nhds (half_pos (sub_pos.mpr hρB)))] with k hk
  filter_upwards [hs k] with x hx
  have hd := (abs_le.mp (pointed_radial_distance (hr k) (hρ.trans hρS) (hv k)
    (hx.trans (mul_le_mul_of_nonneg_right hρS (hr k).le)))).2
  have hx' := (div_le_iff₀ (hr k)).mpr hx
  rw [mem_closedBall,dist_zero_right]
  linarith

omit [BorelSpace X] in
theorem pointed_local_value_integrals {n : ℕ} {S ρ B : ℝ}
    (hρ : 0≤ρ) (hρS : ρ≤S) (hρB : ρ<B)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (hm : ∀ k, Measurable (v k)) (σ : ℕ → ProbabilityMeasure X)
    (hs : ∀ k, ∀ᵐ x ∂(σ k : Measure X), dist x (p k)≤ρ*r k)
    {α : ProbabilityMeasure (Euclidean n)}
    (hweak : Tendsto (fun k => (σ k).map (v k)) atTop (𝓝 α))
    (u : ℕ → X → ℝ) (hi : ∀ k, Integrable (u k) (σ k : Measure X))
    {g : Euclidean n → ℝ} {L : ℝ≥0} (hg : LipschitzOnWith L g (closedBall 0 B))
    (hclose : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(σ k : Measure X), |u k x-g (v k x)|≤δ) :
    Tendsto (fun k => ∫ x, u k x ∂(σ k : Measure X)) atTop
      (𝓝 (∫ z, g z ∂(α : Measure (Euclidean n)))) := by
  obtain ⟨F,hF⟩ := bounded_local_representative (hρ.trans hρB.le) hg
  have himage := pointed_measure_image_support hρ hρS hρB p r ε v hr hεlim hv σ hs
  have hα : ∀ᵐ z ∂(α : Measure (Euclidean n)), z∈closedBall (0:Euclidean n) B := by
    apply weak_limit_ae_closed _ hweak isClosed_closedBall
    filter_upwards [himage] with k hk
    rw [ProbabilityMeasure.toMeasure_map]
    exact (ae_map_iff (hm k).aemeasurable measurableSet_closedBall).mpr hk
  have ht := weak_map_uniform_integrals σ v hm hweak u hi F (by
    intro δ hδ
    filter_upwards [himage,hclose δ hδ] with k hk he
    filter_upwards [hk,he] with x hx hex
    rwa [hF hx])
  have heq : (∫ z, F z ∂(α : Measure (Euclidean n)))=∫ z, g z ∂(α : Measure (Euclidean n)) :=
    integral_congr_ae (hα.mono fun _ hz => hF hz)
  rwa [heq] at ht

end RegularPointCoordinates

end

end OAI
