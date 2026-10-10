import OAI.Probability.FreeIsing.Conditioning.ContinuousCopyImmersion
import OAI.Probability.FreeIsing.Ising.CanonicalMartingales
import OAI.Probability.FreeIsing.Ising.CopyBrownian

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation ContinuousObservationHistory ContinuousCopyBrownian

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

lemma stoppedArray_comap_eq_IsingFiltration (t : ℝ≥0) :
    MeasurableSpace.comap (stoppedArray (ι := TreeVertex d) t) inferInstance = filtration d t := by
  exact stoppedArray_comap_eq_natural t

lemma measurable_observation_singleFiltration (t : ℝ≥0) :
    Measurable[singleFiltration (ι := TreeVertex d) t, filtration d t]
      (Prod.snd : Paths d × Paths d → Paths d) := by
  apply Measurable.of_comap_le
  rw [← stoppedArray_comap_eq_IsingFiltration, MeasurableSpace.comap_comp]
  exact (measurable_snd.comp (comap_measurable (singleHistory t))).comap_le

lemma graphPast_comap_le (beta : ℝ) (t : ℝ≥0) :
    (singleFiltration (ι := TreeVertex d) t).comap
      (fun x : Paths d => (innovationMap beta x, x)) ≤ filtration d t := by
  change (MeasurableSpace.comap (singleHistory t)
    (inferInstance : MeasurableSpace (Paths d × Paths d))).comap
      (fun x : Paths d => (innovationMap beta x, x)) ≤ _
  rw [MeasurableSpace.comap_comp]
  have hW : Measurable[filtration d t]
      (fun x : Paths d => stoppedArray t (innovationMap beta x)) :=
    measurable_stoppedArray_of_eval (mΩ := filtration d t) t (innovationMap beta)
      (fun v s hs => ((innovationMap_stronglyAdapted beta v s).measurable).mono
        ((filtration d).mono hs) le_rfl)
  have hX : Measurable[filtration d t] (stoppedArray (ι := TreeVertex d) t) := by
    rw [← stoppedArray_comap_eq_IsingFiltration]
    exact comap_measurable _
  exact (hW.prodMk hX).comap_le

theorem martingale_graph_of_observation
    {M : ℝ≥0 → Paths d → ℝ}
    (hM : Martingale M (filtration d) (observationLaw μ)) :
    Martingale (fun t (q : Paths d × Paths d) => M t q.2)
      singleFiltration (((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ) := by
  rw [kernel_graphLaw]
  have hgraph : MeasurePreserving (fun x : Paths d => (innovationMap beta x, x))
      (observationLaw μ) (IsingConditionalCopyBounds.graphLaw beta μ) :=
    ⟨(measurable_innovationMap beta).prodMk measurable_id, rfl⟩
  exact MartingalePushforward.martingale_of_pullback hgraph
    (F := filtration d) (G := singleFiltration) (graphPast_comap_le beta)
    (fun t => (hM.stronglyAdapted t).comp_measurable
      (measurable_observation_singleFiltration t)) hM

theorem martingale_copy_projection
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    {M : ℝ≥0 → Paths d → ℝ}
    (hM : Martingale M (filtration d) (observationLaw μ)) (j : Bool) :
    Martingale (fun t (q : IsingCopyEnergy.Joint d) => M t (IsingCopyEnergy.projection j q))
      ContinuousCopyBrownian.joinedFiltration (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  have hg := martingale_graph_of_observation (beta := beta) hM
  cases j
  · exact martingale_right_of_future_indep _ _ (IsingCopyBrownian.graph_future_indep hμ) hg
  · exact martingale_left_of_future_indep _ _ (IsingCopyBrownian.graph_future_indep hμ) hg

theorem copyContinuousPosterior_martingale
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (j : Bool) :
    Martingale (copyContinuousPosterior beta v j)
      ContinuousCopyBrownian.joinedFiltration (copies beta μ) :=
  martingale_copy_projection hμ (continuousPosterior_martingale hd hμ hb hcrit v) j

theorem copyContinuousPosterior_compensatedSquare_martingale
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (j : Bool) :
    Martingale (fun t (q : IsingCopyEnergy.Joint d) => copyContinuousPosterior beta v j t q ^ 2 -
      canonicalCovarianceCompensator beta v t (IsingCopyEnergy.projection j q))
      ContinuousCopyBrownian.joinedFiltration (copies beta μ) :=
  martingale_copy_projection hμ
    (continuousPosterior_compensatedSquare_martingale hd hμ hb hcrit v) j

end Problem367.IsingObservationFactor

end

end OAI
