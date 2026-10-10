import OAI.Geometry.RCD.Metric.MeasuredDensitySources
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Compact Euclidean densities give actual interior source probabilities -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.measured_compact_density_sources {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S ρ τ : ℝ} (hS : 0<S) (hρτ : ρ<τ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (a : Euclidean n →ᵇ ℝ) (ha : ∀ z, 0≤a z)
    (ha0 : ∀ z, ρ≤‖z‖ → a z=0)
    (hpos : 0<∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    ∃ N : ℕ, ∃ ν : ℕ → ProbabilityMeasure X, ∃ c : ℕ → ℝ,
      (∀ k, 0≤c k) ∧
      Tendsto c atTop (𝓝 ((∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖a‖)) ∧
      (∀ k, (ν k : Measure X)≤
        (ENNReal.ofReal (c k)*(hausdorff n X (ball (p (k+N)) (S*r (k+N))))⁻¹) • hausdorff n X) ∧
      (∀ k, ∀ᵐ x ∂(ν k : Measure X), dist x (p (k+N))≤τ*r (k+N)) ∧
      Tendsto (fun k => (ν k).map (v (k+N))) atTop
        (𝓝 (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
          (a.integrable _) ha hpos)) := by
  obtain ⟨N,ν,c,hc,hcl,hb,hs,hn,hw⟩ :=
    hX.measured_density_sources_nonzero hS p r ε v hr hε hv a ha hpos
  have he := (hε.comp (tendsto_add_atTop_nat N)).eventually
    (Iio_mem_nhds (show 0<(τ-ρ)/3 by linarith))
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  refine ⟨M+N,(fun k => ν (k+M)),(fun k => c (k+M)),(fun k => hc (k+M)),
    hcl.comp (tendsto_add_atTop_nat M),?_,?_,?_⟩
  · intro k
    simpa only [Function.comp_def,Nat.add_assoc] using hb (k+M)
  · intro k
    have heps : ε ((k+M)+N)<(τ-ρ)/3 := hM (k+M) (Nat.le_add_left M k)
    filter_upwards [hs (k+M),hn (k+M)] with x hx hnx
    have hnorm : ‖v ((k+M)+N) x‖<ρ := lt_of_not_ge (fun hh => hnx (ha0 _ hh))
    have hd := (abs_le.mp (pointed_radial_distance (hr ((k+M)+N)) hS.le
      (hv ((k+M)+N)).metric (le_of_lt hx))).1
    have hdist : dist x (p ((k+M)+N))≤τ*r ((k+M)+N) := by
      apply (div_le_iff₀ (hr ((k+M)+N))).mp
      linarith
    simpa only [Function.comp_def,Nat.add_assoc] using hdist
  · simpa only [Function.comp_def,Nat.add_assoc] using hw.comp (tendsto_add_atTop_nat M)

end RegularPointCoordinates

end

end OAI
