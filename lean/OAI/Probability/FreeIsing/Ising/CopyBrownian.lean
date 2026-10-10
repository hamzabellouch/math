import OAI.Probability.FreeIsing.Conditioning.ContinuousCopyIndependence
import OAI.Probability.FreeIsing.Ising.ObservationComparison
import OAI.Probability.FreeIsing.Ising.ObservationIndependence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyBrownian

open IsingObservationInnovation IsingObservationFactor
open ContinuousObservationHistory ContinuousNoiseSplit

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem graph_future_indep
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s : ℝ≥0) :
    IndepFun (fun q : Paths d × Paths d =>
      (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1)
      (((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ) := by
  rw [kernel_graphLaw]
  unfold IsingConditionalCopyBounds.graphLaw
  apply ConstructedConditionalCopies.indepFun_map_of_comp
    ((measurable_innovationMap beta).prodMk measurable_id)
    (((measurable_stoppedArray s).comp measurable_fst).prodMk
      ((measurable_stoppedArray s).comp measurable_snd))
    ((measurable_futureArray s).comp measurable_fst)
  exact ConstructedContinuousCopies.indepFun_continuous_future
    (observationLaw μ) (filtration d) (innovationMap beta) id
    (fun v t => (innovationMap_stronglyAdapted beta v t).measurable)
    (fun v t => (arrayNaturalFiltration_stronglyAdapted
      evaluation measurable_evaluation v t).measurable)
    (innovationMap_increment_indep_filtration hμ) s

theorem future_indep_joinedFiltration
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap
      (fun q : Paths d × (Paths d × Paths d) => futureArray s q.1) inferInstance)
      (ContinuousCopyBrownian.joinedFiltration s) (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  exact ContinuousCopyBrownian.indep_future_joinedFiltration
    ((observationLaw μ).map (innovationMap beta)) (kernel beta μ) s
    (graph_future_indep hμ s)

theorem increment_indep_joinedFiltration
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun q : Paths d × (Paths d × Paths d) => fun v => q.1 v t - q.1 v s)
      inferInstance) (ContinuousCopyBrownian.joinedFiltration s) (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  exact ContinuousCopyBrownian.indep_increment_joinedFiltration
    ((observationLaw μ).map (innovationMap beta)) (kernel beta μ) hst
    (graph_future_indep hμ s)

theorem commonNoise_stronglyAdapted (v : TreeVertex d) :
    StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : Paths d × (Paths d × Paths d)) => q.1 v t) := by
  intro t
  exact ((measurable_pi_apply v).comp
    (ContinuousCopyBrownian.measurable_commonNoise_joinedFiltration t)).stronglyMeasurable

omit [IsProbabilityMeasure μ] in
private theorem innovationLaw_coordinate_preBrownian [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    IsPreBrownianReal (fun t (w : Paths d) => w v t)
      ((observationLaw μ).map (innovationMap beta)) := by
  rw [map_innovationMap_observationLaw hμ]
  exact ⟨fun I => (WienerSampler.coordinate_isBrownianReal.hasLaw I).comp
    (measurePreserving_eval_infinitePi
      (fun _ : TreeVertex d => WienerSampler.wienerMeasure) v).hasLaw⟩

theorem commonNoise_isBrownianReal
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    IsBrownianReal (fun t (q : Paths d × (Paths d × Paths d)) => q.1 v t)
      (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  exact ContinuousCopyBrownian.isBrownian_commonNoise v
    ((observationLaw μ).map (innovationMap beta))
    (innovationLaw_coordinate_preBrownian hμ v) (kernel beta μ)

theorem commonNoise_martingale
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d) :
    Martingale (fun t (q : Paths d × (Paths d × Paths d)) => q.1 v t)
      ContinuousCopyBrownian.joinedFiltration (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  exact ContinuousCopyBrownian.commonNoise_martingale v
    ((observationLaw μ).map (innovationMap beta))
    (innovationLaw_coordinate_preBrownian hμ v) (kernel beta μ)
    (graph_future_indep hμ)

theorem commonNoise_increments_indep
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (s t : ℝ≥0)
    {v w : TreeVertex d} (hvw : v ≠ w) :
    IndepFun (fun q : Paths d × (Paths d × Paths d) => q.1 v t - q.1 v s)
      (fun q => q.1 w t - q.1 w s) (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  have hp : MeasurePreserving (Prod.fst : Paths d × (Paths d × Paths d) → Paths d)
      (copies beta μ) ((observationLaw μ).map (innovationMap beta)) :=
    ⟨measurable_fst, Measure.fst_compProd _ _⟩
  apply indepFun_comp_measurePreserving hp
    ((measurable_evaluation v t).sub (measurable_evaluation v s))
    ((measurable_evaluation w t).sub (measurable_evaluation w s))
  rw [map_innovationMap_observationLaw hμ]
  exact (iIndepFun_infinitePi (P := fun _ : TreeVertex d => WienerSampler.wienerMeasure)
    (fun _ => (continuous_eval_const t).measurable.sub
      (continuous_eval_const s).measurable)).indepFun hvw

end Problem367.IsingCopyBrownian

end

end OAI
