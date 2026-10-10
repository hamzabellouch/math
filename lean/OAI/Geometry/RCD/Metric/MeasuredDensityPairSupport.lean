import OAI.Geometry.RCD.Metric.MeasuredCompactDensitySupport

namespace OAI

/-! # A common source tail preserving both exact density supports -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.measured_density_pair_nonzero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S ρ τ : ℝ} (hS : 0<S) (hρτ : ρ<τ)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (a b : Euclidean n →ᵇ ℝ) (ha : ∀ z, 0≤a z) (hb : ∀ z, 0≤b z)
    (ha0 : ∀ z, ρ≤‖z‖ → a z=0) (hb0 : ∀ z, ρ≤‖z‖ → b z=0)
    (hapos : 0<∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))
    (hbpos : 0<∫ z, b z ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    ∃ N : ℕ, ∃ ν₀ ν₁ : ℕ → ProbabilityMeasure X, ∃ c : ℕ → ℝ,
      (∀ k, 0≤c k) ∧
      Tendsto c atTop (𝓝 (max
        ((∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖a‖)
        ((∫ z, b z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖b‖))) ∧
      (∀ k, (ν₀ k : Measure X)≤
        (ENNReal.ofReal (c k)*(hausdorff n X (ball (p (k+N)) (S*r (k+N))))⁻¹) • hausdorff n X) ∧
      (∀ k, (ν₁ k : Measure X)≤
        (ENNReal.ofReal (c k)*(hausdorff n X (ball (p (k+N)) (S*r (k+N))))⁻¹) • hausdorff n X) ∧
      (∀ k, ∀ᵐ x ∂(ν₀ k : Measure X), dist x (p (k+N))≤τ*r (k+N)) ∧
      (∀ k, ∀ᵐ x ∂(ν₁ k : Measure X), dist x (p (k+N))≤τ*r (k+N)) ∧
      (∀ k, ∀ᵐ x ∂(ν₀ k : Measure X), a (v (k+N) x)≠0) ∧
      (∀ k, ∀ᵐ x ∂(ν₁ k : Measure X), b (v (k+N) x)≠0) ∧
      Tendsto (fun k => (ν₀ k).map (v (k+N))) atTop
        (𝓝 (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
          (a.integrable _) ha hapos)) ∧
      Tendsto (fun k => (ν₁ k).map (v (k+N))) atTop
        (𝓝 (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
          (b.integrable _) hb hbpos)) := by
  obtain ⟨N₀,ν₀,c₀,hc₀,hc₀lim,hbound₀,hs₀,hn₀,hw₀⟩ :=
    hX.measured_compact_density_sources_nonzero hS hρτ p r ε v hr hε hv a ha ha0 hapos
  obtain ⟨N₁,ν₁,c₁,hc₁,hc₁lim,hbound₁,hs₁,hn₁,hw₁⟩ :=
    hX.measured_compact_density_sources_nonzero hS hρτ
      (fun k => p (k+N₀)) (fun k => r (k+N₀)) (fun k => ε (k+N₀)) (fun k => v (k+N₀))
      (fun k => hr (k+N₀)) (hε.comp (tendsto_add_atTop_nat N₀)) (fun k => hv (k+N₀))
      b hb hb0 hbpos
  have hmono {a b : ℝ≥0∞} (hab : a≤b) : a • hausdorff n X≤b • hausdorff n X := by
    intro s
    simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul' hab (le_refl (hausdorff n X s))
  let c := fun k => max (c₀ (k+N₁)) (c₁ k)
  refine ⟨N₁+N₀,(fun k => ν₀ (k+N₁)),ν₁,c,
    (fun k => (hc₀ (k+N₁)).trans (le_max_left _ _)),
    (hc₀lim.comp (tendsto_add_atTop_nat N₁)).max hc₁lim,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k
    have hh := (hbound₀ (k+N₁)).trans (hmono
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left (c₀ (k+N₁)) (c₁ k))) le_rfl))
    simpa only [Function.comp_def,Nat.add_assoc] using hh
  · intro k
    have hh := (hbound₁ k).trans (hmono
      (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right (c₀ (k+N₁)) (c₁ k))) le_rfl))
    simpa only [Function.comp_def,Nat.add_assoc] using hh
  · intro k
    simpa only [Function.comp_def,Nat.add_assoc] using hs₀ (k+N₁)
  · intro k
    simpa only [Function.comp_def,Nat.add_assoc] using hs₁ k
  · intro k
    simpa only [Function.comp_def,Nat.add_assoc] using hn₀ (k+N₁)
  · intro k
    simpa only [Function.comp_def,Nat.add_assoc] using hn₁ k
  · simpa only [Function.comp_def,Nat.add_assoc] using hw₀.comp (tendsto_add_atTop_nat N₁)
  · simpa only [Function.comp_def,Nat.add_assoc] using hw₁

end RegularPointCoordinates

end

end OAI
