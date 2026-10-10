import OAI.Probability.FreeIsing.Conditioning.CopyImmersion
import OAI.Probability.FreeIsing.Martingales.Pushforward
import OAI.Probability.FreeIsing.Stochastic.ContinuousCopyBrownian

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.ContinuousCopyBrownian
open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι : Type*}

def singleHistory (s : ℝ≥0) (q : (ι → Path) × (ι → Path)) :=
  (stoppedArray s q.1, stoppedArray s q.2)

lemma measurable_singleHistory (s : ℝ≥0) : Measurable (singleHistory (ι := ι) s) :=
  ((measurable_stoppedArray s).comp measurable_fst).prodMk
    ((measurable_stoppedArray s).comp measurable_snd)

lemma singleHistory_singleHistory {s t : ℝ≥0} (hst : s ≤ t)
    (q : (ι → Path) × (ι → Path)) : singleHistory s (singleHistory t q) = singleHistory s q := by
  simp only [singleHistory, stoppedArray_stoppedArray hst]

def singleFiltration : Filtration ℝ≥0
    (inferInstance : MeasurableSpace ((ι → Path) × (ι → Path))) where
  seq s := MeasurableSpace.comap (singleHistory s) inferInstance
  mono' := by
    intro s t hst
    have h := MeasurableSpace.comap_mono (g := singleHistory (ι := ι) t)
      (measurable_singleHistory s).comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      singleHistory_singleHistory hst] using h
  le' s := (measurable_singleHistory s).comap_le

lemma measurable_noisePast_singleFiltration (s : ℝ≥0) :
    Measurable[singleFiltration (ι := ι) s]
      (fun q : (ι → Path) × (ι → Path) => stoppedArray s q.1) :=
  measurable_fst.comp (comap_measurable (singleHistory s))

lemma joinedFiltration_eq_left (s : ℝ≥0) :
    joinedFiltration (ι := ι) s =
      (singleFiltration s).comap (fun q : Joint (ι := ι) => (q.1, q.2.1)) ⊔
      MeasurableSpace.comap (fun q : Joint (ι := ι) => stoppedArray s q.2.2) inferInstance := by
  change MeasurableSpace.comap
    (fun q : Joint (ι := ι) =>
      (stoppedArray s q.1, (stoppedArray s q.2.1, stoppedArray s q.2.2)))
    ((inferInstance : MeasurableSpace (ι → Path)).prod
      ((inferInstance : MeasurableSpace (ι → Path)).prod
        (inferInstance : MeasurableSpace (ι → Path)))) = _
  simp only [singleFiltration, singleHistory, MeasurableSpace.comap_comp,
    Function.comp_def]
  change MeasurableSpace.comap
    (fun q : Joint (ι := ι) =>
      (stoppedArray s q.1, (stoppedArray s q.2.1, stoppedArray s q.2.2)))
    ((inferInstance : MeasurableSpace (ι → Path)).prod
      ((inferInstance : MeasurableSpace (ι → Path)).prod
        (inferInstance : MeasurableSpace (ι → Path)))) =
      MeasurableSpace.comap
        (fun q : Joint (ι := ι) => (stoppedArray s q.1, stoppedArray s q.2.1))
        ((inferInstance : MeasurableSpace (ι → Path)).prod
          (inferInstance : MeasurableSpace (ι → Path))) ⊔
      MeasurableSpace.comap (fun q : Joint (ι := ι) => stoppedArray s q.2.2) inferInstance
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_prodMk,
    MeasurableSpace.comap_prodMk, sup_assoc]

theorem exists_past_kernel [Countable ι]
    (ρ : Measure (ι → Path)) [IsProbabilityMeasure ρ]
    (η : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel η] (s : ℝ≥0)
    (hind : IndepFun (singleHistory s)
      (fun q : (ι → Path) × (ι → Path) => futureArray s q.1) (ρ ⊗ₘ η)) :
    ∃ κ : Kernel (ι → Path) (ι → Path), IsMarkovKernel κ ∧
      (fun w => (η.map (stoppedArray s)) w) =ᵐ[ρ]
        fun w => κ (stoppedArray s w) :=
  ConditionalCopyImmersion.exists_past_kernel_of_reconstructible_split ρ
    (stoppedArray s) (measurable_stoppedArray s)
    (futureArray s) (measurable_futureArray s) (measurableEmbedding_split s)
    η (stoppedArray s) (measurable_stoppedArray s) hind

theorem martingale_left_of_future_indep [Countable ι]
    (ρ : Measure (ι → Path)) [IsProbabilityMeasure ρ]
    (η : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel η]
    (hind : ∀ s, IndepFun (singleHistory s)
      (fun q : (ι → Path) × (ι → Path) => futureArray s q.1) (ρ ⊗ₘ η))
    {M : ℝ≥0 → (ι → Path) × (ι → Path) → ℝ}
    (hM : Martingale M singleFiltration (ρ ⊗ₘ η)) :
    Martingale (fun t (q : Joint (ι := ι)) => M t (q.1, q.2.1))
      joinedFiltration (ρ ⊗ₘ (η ×ₖ η)) := by
  exact ConditionalCopyImmersion.martingale_left ρ η
    stoppedArray measurable_stoppedArray stoppedArray measurable_stoppedArray
    singleFiltration joinedFiltration joinedFiltration_eq_left
    measurable_noisePast_singleFiltration
    (fun s => exists_past_kernel ρ η s (hind s)) hM

lemma measurable_swap_joinedFiltration (s : ℝ≥0) :
    Measurable[joinedFiltration (ι := ι) s, joinedFiltration s]
      (fun q : Joint (ι := ι) => (q.1, (q.2.2, q.2.1))) := by
  apply Measurable.of_comap_le
  change (MeasurableSpace.comap (history s)
    (inferInstance : MeasurableSpace (Joint (ι := ι)))).comap
      (fun q : Joint (ι := ι) => (q.1, (q.2.2, q.2.1))) ≤ _
  rw [MeasurableSpace.comap_comp]
  have hh : Measurable[joinedFiltration (ι := ι) s] (history s) := comap_measurable _
  have hm := (measurable_fst.comp hh).prodMk
    (((measurable_snd.comp measurable_snd).comp hh).prodMk
      ((measurable_fst.comp measurable_snd).comp hh))
  exact hm.comap_le

theorem martingale_right_of_future_indep [Countable ι]
    (ρ : Measure (ι → Path)) [IsProbabilityMeasure ρ]
    (η : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel η]
    (hind : ∀ s, IndepFun (singleHistory s)
      (fun q : (ι → Path) × (ι → Path) => futureArray s q.1) (ρ ⊗ₘ η))
    {M : ℝ≥0 → (ι → Path) × (ι → Path) → ℝ}
    (hM : Martingale M singleFiltration (ρ ⊗ₘ η)) :
    Martingale (fun t (q : Joint (ι := ι)) => M t (q.1, q.2.2))
      joinedFiltration (ρ ⊗ₘ (η ×ₖ η)) := by
  have hl := martingale_left_of_future_indep ρ η hind hM
  apply MartingalePushforward.martingale_of_pullback
    (ConditionalCopyImmersion.swap_measurePreserving ρ η)
    (F := joinedFiltration) (G := joinedFiltration)
    (fun t => (measurable_swap_joinedFiltration t).comap_le)
    (fun t => (hl.stronglyAdapted t).comp_measurable (measurable_swap_joinedFiltration t))
  exact hl

end Problem367.ContinuousCopyBrownian

end

end OAI
