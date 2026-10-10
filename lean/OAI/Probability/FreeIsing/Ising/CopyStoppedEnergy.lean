import OAI.Probability.FreeIsing.Ising.ObservationComparison
import OAI.Probability.FreeIsing.Martingales.StoppedDiscrepancyEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

theorem ae_all_field_difference_version_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {X : ℝ≥0 → (Paths d × (Paths d × Paths d)) → ℝ}
    (hc : ∀ᵐ q ∂copies beta μ, Continuous (fun t => X t q))
    (hver : ∀ t, X t =ᵐ[copies beta μ]
      (fun q => field beta v t q.2.1 - field beta v t q.2.2)) :
    ∀ᵐ q ∂copies beta μ, ∀ t, |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  have hfixed (t : ℝ≥0) : ∀ᵐ q ∂copies beta μ,
      |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
    filter_upwards [hver t, IsingConditionalCopyBounds.ae_fieldDifference_bound
      hμ hb kernel_graphLaw t v] with q hq hbound
    exact hq ▸ hbound
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let : Countable S := hSc.to_subtype
  have hS : ∀ᵐ q ∂copies beta μ, ∀ t : S,
      |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta :=
    ae_all_iff.mpr (fun t => hfixed t)
  filter_upwards [hc, hS] with q hqc hSq
  refine isClosed_property hSd.denseRange_val
    (p := fun t : ℝ≥0 => |X t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta) ?_ hSq
  exact isClosed_le hqc.abs
    ((continuous_const.mul continuous_subtype_val).add continuous_const)

theorem ae_horizon_field_difference_version_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d) {X : ℝ≥0 → (Paths d × (Paths d × Paths d)) → ℝ}
    (hc : ∀ᵐ q ∂copies beta μ, Continuous (fun t => X t q))
    (hver : ∀ t, X t =ᵐ[copies beta μ]
      (fun q => field beta v t q.2.1 - field beta v t q.2.2)) (T : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ t ≤ T,
      |X t q| ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  filter_upwards [ae_all_field_difference_version_bound hμ hb v hc hver] with q hq
  intro t ht
  exact (hq t).trans (by gcongr)

theorem field_difference_energy_analysis_of_stopped_version
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d)
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Paths d × (Paths d × Paths d)))}
    {X : ℝ≥0 → (Paths d × (Paths d × Paths d)) → ℝ}
    (hX : IsStronglyProgressive F X)
    (hc : ∀ᵐ q ∂copies beta μ, Continuous (fun t => X t q))
    (hver : ∀ t, X t =ᵐ[copies beta μ]
      (fun q => field beta v t q.2.1 - field beta v t q.2.2))
    {τ : ℕ → (Paths d × (Paths d × Paths d)) → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime F (τ n)) {T : ℝ≥0}
    (hexit : ∀ᵐ q ∂copies beta μ, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n q)
    {E : ℝ → (Paths d × (Paths d × Paths d)) → ℝ}
    (hE : Integrable (fun p : ℝ × (Paths d × (Paths d × Paths d)) => E p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod (copies beta μ)))
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ q, (stoppedProcess X (τ n) t q) ^ 2 ∂copies beta μ) =
        (∫ q, (X 0 q) ^ 2 ∂copies beta μ) + ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ q, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n q then E s q else 0 ∂copies beta μ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ q,
      (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        deriv (fun s : ℝ => ∫ q,
          (field beta v s.toNNReal q.2.1 - field beta v s.toNNReal q.2.2) ^ 2
            ∂copies beta μ) t = ∫ q, E t q ∂copies beta μ) := by
  have heq (t : ℝ≥0) : (∫ q, (X t q) ^ 2 ∂copies beta μ) =
      ∫ q, (field beta v t q.2.1 - field beta v t q.2.2) ^ 2 ∂copies beta μ :=
    integral_congr_ae ((hver t).mono (fun q hq => congrArg (fun x : ℝ => x ^ 2) hq))
  simpa only [heq] using DiscrepancyEnergy.secondMoment_analysis_of_stopped hX hτ
    (ae_horizon_field_difference_version_bound hμ hb v hc hver T) hexit hE hlocal

end Problem367.IsingObservationFactor

end

end OAI
