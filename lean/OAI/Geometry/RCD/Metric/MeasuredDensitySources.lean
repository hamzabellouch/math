import OAI.Geometry.RCD.Metric.DensityLawSupport
import OAI.Geometry.RCD.Coordinates.NormalizedLawCompression
import OAI.Geometry.RCD.Metric.MeasuredBallLaw

namespace OAI

/-! # Actual bounded-density source measures for Euclidean transport tests -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.measured_density_sources_nonzero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (a : Euclidean n →ᵇ ℝ) (ha : ∀ z, 0≤a z)
    (hpos : 0<∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    ∃ N : ℕ, ∃ ν : ℕ → ProbabilityMeasure X, ∃ c : ℕ → ℝ,
      (∀ k, 0≤c k) ∧
      Tendsto c atTop (𝓝 ((∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖a‖)) ∧
      (∀ k, (ν k : Measure X)≤
        (ENNReal.ofReal (c k)*(hausdorff n X (ball (p (k+N)) (S*r (k+N))))⁻¹) • hausdorff n X) ∧
      (∀ k, ∀ᵐ x ∂(ν k : Measure X), x∈ball (p (k+N)) (S*r (k+N))) ∧
      (∀ k, ∀ᵐ x ∂(ν k : Measure X), a (v (k+N) x)≠0) ∧
      Tendsto (fun k => (ν k).map (v (k+N))) atTop
        (𝓝 (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
          (a.integrable _) ha hpos)) := by
  let μ := hausdorff n X
  let U := fun k => ball (p k) (S*r k)
  let : Nonempty X := ⟨p 0⟩
  let : ∀ k, IsFiniteMeasure (μ.restrict (U k)) := fun k =>
    ⟨by simpa only [Measure.restrict_apply_univ] using (hX.finiteOnBounded _ isBounded_ball)⟩
  have hmass (k : ℕ) : 0<μ.real (U k) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hne (k : ℕ) : μ.restrict (U k)≠0 := by
    intro hh
    have hz := congrArg (fun m : Measure X => m.real univ) hh
    have hz' : μ.real (U k)=0 := by simpa only [Measure.real,Measure.restrict_apply_univ,
      Measure.coe_zero,Pi.zero_apply,ENNReal.toReal_zero] using hz
    exact (hmass k).ne' hz'
  let P := fun k => normalizedProbabilityLaw (μ.restrict (U k))
  have hweak : Tendsto (fun k => (P k).map (v k)) atTop (𝓝 (euclideanBallProbability n S)) :=
    measured_approximation_laws_tendsto hS hv
      (fun _ => (hX.finiteOnBounded _ isBounded_ball).ne) hmass hε
  let m := fun k => ∫ x, a (v k x) ∂(P k : Measure X)
  have hm := pullback_density_mass_tendsto P v (fun k => (hv k).measurable) hweak a
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.eventually (Ioi_mem_nhds hpos))
  have hmpos (k : ℕ) : 0 < m (k+N) := hN (k+N) (Nat.le_add_left N k)
  let ν := fun k => pullbackDensityLaw (P (k+N)) (v (k+N)) (hv (k+N)).measurable a ha (hmpos k)
  let c := fun k => (m (k+N))⁻¹*‖a‖
  have hbase (k : ℕ) : (ν k : Measure X)≤ENNReal.ofReal (c k) • (P (k+N) : Measure X) := by
    apply normalizedDensityLaw_le
    exact fun x => (le_abs_self _).trans (a.norm_coe_le_norm (v (k+N) x))
  refine ⟨N,ν,c,(fun k => mul_nonneg (inv_nonneg.mpr (hmpos k).le) (norm_nonneg a)),?_,?_,?_,?_,?_⟩
  · exact ((hm.comp (tendsto_add_atTop_nat N)).inv₀ hpos.ne').mul_const ‖a‖
  · intro k
    have hp := hbase k
    rw [normalizedProbabilityLaw_measure _ (hne (k+N)),smul_smul,Measure.restrict_apply_univ] at hp
    exact hp.trans (smul_le_smul_left _ Measure.restrict_le_self)
  · intro k
    exact (Measure.absolutelyContinuous_of_le_smul (hbase k)).ae_le
      (normalized_restriction_ae_mem μ measurableSet_ball (hne (k+N)))
  · exact fun k => pullbackDensityLaw_ae_ne_zero (P (k+N)) (v (k+N))
      (hv (k+N)).measurable a ha (hmpos k)
  · exact pullback_density_laws_tendsto (fun k => P (k+N)) (fun k => v (k+N))
      (fun k => (hv (k+N)).measurable) (hweak.comp (tendsto_add_atTop_nat N)) a ha hpos hmpos

/-- Original interface retained for existing callers. -/
theorem NoncollapsedRCD.measured_density_sources {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S : ℝ} (hS : 0<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (a : Euclidean n →ᵇ ℝ) (ha : ∀ z, 0≤a z)
    (hpos : 0<∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    ∃ N : ℕ, ∃ ν : ℕ → ProbabilityMeasure X, ∃ c : ℕ → ℝ,
      (∀ k, 0≤c k) ∧
      Tendsto c atTop (𝓝 ((∫ z, a z ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖a‖)) ∧
      (∀ k, (ν k : Measure X)≤
        (ENNReal.ofReal (c k)*(hausdorff n X (ball (p (k+N)) (S*r (k+N))))⁻¹) • hausdorff n X) ∧
      (∀ k, ∀ᵐ x ∂(ν k : Measure X), x∈ball (p (k+N)) (S*r (k+N))) ∧
      Tendsto (fun k => (ν k).map (v (k+N))) atTop
        (𝓝 (normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
          (a.integrable _) ha hpos)) := by
  obtain ⟨N,ν,c,hc,hcl,hb,hs,_,hw⟩ :=
    hX.measured_density_sources_nonzero hS p r ε v hr hε hv a ha hpos
  exact ⟨N,ν,c,hc,hcl,hb,hs,hw⟩

end RegularPointCoordinates

end

end OAI
