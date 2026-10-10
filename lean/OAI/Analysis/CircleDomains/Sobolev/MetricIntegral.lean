import OAI.Analysis.CircleDomains.Sobolev.MetricEnergy

namespace OAI

/-!
# Integrating the finite-transfer metric limit

The original trace bounds the regularized energy density uniformly. Dominated
convergence therefore turns the scalar eigenvalue limit into the small-energy
choice used in Step 5 of finite transfer. The eigenvalues need only be
measurable with integrable trace; smooth compact pieces satisfy these hypotheses.
-/

open Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity.FiniteTransfer

noncomputable section

/-- Measurability of the regularized metric energy. -/
theorem measurable_metricEnergy {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) (τ : ℝ) :
    Measurable (fun x => metricEnergy (a x) (b x) τ) := by
  unfold metricEnergy
  exact ((ha.mul (hb.add_const τ).sqrt).div (ha.add_const τ).sqrt).add
    ((hb.mul (ha.add_const τ).sqrt).div (hb.add_const τ).sqrt)

/-- Dominated convergence for the optimized metric: the limiting total
energy is twice the integral of the square root of the determinant. -/
theorem tendsto_integral_metricEnergy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (htrace : Integrable (fun x => a x + b x) μ) :
    Tendsto (fun τ : ℝ => ∫ x, metricEnergy (a x) (b x) τ ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, 2 * Real.sqrt (a x * b x) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => a x + b x)
  · exact Filter.Eventually.of_forall fun τ => (measurable_metricEnergy ha hb τ).aestronglyMeasurable
  · have hpos : ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ := self_mem_nhdsWithin
    filter_upwards [hpos] with τ hτ
    apply Filter.Eventually.of_forall
    intro x
    have hn : 0 ≤ metricEnergy (a x) (b x) τ := by
      have hax := ha0 x
      have hbx := hb0 x
      unfold metricEnergy
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact metricEnergy_le_trace (ha0 x) (hb0 x) hτ
  · exact htrace
  · exact Filter.Eventually.of_forall fun x => tendsto_metricEnergy (ha0 x) (hb0 x)

/-- A sufficiently small positive regularization attains any strict upper
bound for the limiting determinant integral. -/
theorem exists_metricEnergy_integral_lt {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (htrace : Integrable (fun x => a x + b x) μ) {ε : ℝ}
    (hε : (∫ x, 2 * Real.sqrt (a x * b x) ∂μ) < ε) :
    ∃ τ : ℝ, 0 < τ ∧ (∫ x, metricEnergy (a x) (b x) τ ∂μ) < ε := by
  have hlim := tendsto_integral_metricEnergy ha hb ha0 hb0 htrace
  have hsmall := hlim.eventually (gt_mem_nhds hε)
  have hpos : ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 < τ := self_mem_nhdsWithin
  exact (hpos.and hsmall).exists

/-- On a rank-at-most-one piece, the total regularized energy tends to zero. -/
theorem tendsto_integral_metricEnergy_rank_one {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (ha0 : ∀ x, 0 ≤ a x) (hb0 : ∀ x, 0 ≤ b x)
    (htrace : Integrable (fun x => a x + b x) μ) (hrank : ∀ x, a x * b x = 0) :
    Tendsto (fun τ : ℝ => ∫ x, metricEnergy (a x) (b x) τ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  simpa [hrank] using tendsto_integral_metricEnergy ha hb ha0 hb0 htrace

end

end CircleDomainRigidity.FiniteTransfer

end OAI
