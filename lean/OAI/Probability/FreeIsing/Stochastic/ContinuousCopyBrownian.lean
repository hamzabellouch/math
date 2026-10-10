import OAI.Probability.FreeIsing.Gaussian.ContinuousNoiseSplit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousCopyBrownian

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι : Type*}

abbrev Joint := (ι → Path) × ((ι → Path) × (ι → Path))

def history (s : ℝ≥0) (q : Joint (ι := ι)) : Joint (ι := ι) :=
  (stoppedArray s q.1, (stoppedArray s q.2.1, stoppedArray s q.2.2))

theorem measurable_history (s : ℝ≥0) : Measurable (history (ι := ι) s) :=
  ((measurable_stoppedArray s).comp measurable_fst).prodMk
    (((measurable_stoppedArray s).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_stoppedArray s).comp (measurable_snd.comp measurable_snd)))

theorem history_history {s t : ℝ≥0} (hst : s ≤ t) (q : Joint (ι := ι)) :
    history s (history t q) = history s q := by
  simp only [history, stoppedArray_stoppedArray hst]

abbrev pastSpace (s : ℝ≥0) : MeasurableSpace (Joint (ι := ι)) :=
  MeasurableSpace.comap (history s) inferInstance

def joinedFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Joint (ι := ι))) where
  seq := pastSpace
  mono' := by
    intro s t hst
    have h := MeasurableSpace.comap_mono (g := history (ι := ι) t) (measurable_history s).comap_le
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, history_history hst] using h
  le' s := (measurable_history s).comap_le

theorem isBrownian_commonNoise
    (i : ι) (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ι → Path) => w i t) rho)
    (eta : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel eta] :
    IsBrownianReal (fun t (q : Joint (ι := ι)) => q.1 i t) (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hmp : MeasurePreserving (Prod.fst : Joint (ι := ι) → (ι → Path))
      (rho ⊗ₘ (eta ×ₖ eta)) rho := ⟨measurable_fst, Measure.fst_compProd _ _⟩
  exact ⟨⟨fun I => (hB.hasLaw I).comp hmp.hasLaw⟩,
    Filter.Eventually.of_forall (fun q => (q.1 i).continuous)⟩

theorem condExp_increment_eq_zero [Countable ι]
    (i : ι) (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ι → Path) => w i t) rho)
    (eta : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel eta]
    {s t : ℝ≥0} (hst : s ≤ t)
    (hind : IndepFun (fun q : (ι → Path) × (ι → Path) =>
      (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta)) :
    (rho ⊗ₘ (eta ×ₖ eta))[(fun q : Joint (ι := ι) => q.1 i t - q.1 i s) |
      pastSpace s] =ᵐ[rho ⊗ₘ (eta ×ₖ eta)] fun _ => 0 := by
  have hcopy := ContinuousNoiseSplit.indepFun_future_conditionalCopies s rho eta
    (stoppedArray s) (measurable_stoppedArray s) hind
  have hf : Measurable (fun w : ι → Path => w i (t - s)) :=
    (continuous_eval_const (t - s)).measurable.comp (measurable_pi_apply i)
  have hi : IndepFun (fun q : Joint (ι := ι) => q.1 i t - q.1 i s) (history s)
      (rho ⊗ₘ (eta ×ₖ eta)) := by
    change IndepFun (fun q : Joint (ι := ι) => q.1 i t - q.1 i s)
      (fun q => (stoppedArray s q.1, (stoppedArray s q.2.1, stoppedArray s q.2.2))) _
    simpa only [Function.comp_def, id_eq, futureArray, futurePath_apply,
      add_tsub_cancel_of_le hst] using hcopy.symm.comp hf measurable_id
  have hm : Measurable (fun q : Joint (ι := ι) => q.1 i t - q.1 i s) :=
    (((continuous_eval_const t).measurable.comp (measurable_pi_apply i)).comp measurable_fst).sub
      (((continuous_eval_const s).measurable.comp (measurable_pi_apply i)).comp measurable_fst)
  have hc := condExp_indep_eq hm.comap_le (measurable_history s).comap_le
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hi
  have hBc := (isBrownian_commonNoise i rho hB eta).toIsPreBrownianReal
  have hz : (∫ q : Joint (ι := ι), q.1 i t - q.1 i s ∂rho ⊗ₘ (eta ×ₖ eta)) = 0 := by
    rw [integral_sub (hBc.integrable_eval t) (hBc.integrable_eval s),
      hBc.integral_eval, hBc.integral_eval, sub_self]
  simpa only [hz] using hc

theorem commonNoise_martingale [Countable ι]
    (i : ι) (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (hB : IsPreBrownianReal (fun t (w : ι → Path) => w i t) rho)
    (eta : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel eta]
    (hind : ∀ s, IndepFun (fun q : (ι → Path) × (ι → Path) =>
      (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta)) :
    Martingale (fun t (q : Joint (ι := ι)) => q.1 i t) joinedFiltration
      (rho ⊗ₘ (eta ×ₖ eta)) := by
  have had : StronglyAdapted (joinedFiltration (ι := ι))
      (fun t (q : Joint (ι := ι)) => q.1 i t) := by
    intro t
    change StronglyMeasurable[pastSpace (ι := ι) t] (fun q : Joint (ι := ι) => q.1 i t)
    have hh : Measurable[pastSpace (ι := ι) t] (history (ι := ι) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply i).comp (measurable_fst.comp hh))
    simpa only [Function.comp_def, history, stoppedArray, stoppedPath_apply, min_self] using hm.stronglyMeasurable
  apply martingale_of_conditional_increment_zero had
    (fun t => (isBrownian_commonNoise i rho hB eta).toIsPreBrownianReal.integrable_eval t)
  intro s t hst
  exact condExp_increment_eq_zero i rho hB eta hst (hind s)

end Problem367.ContinuousCopyBrownian

end

end OAI
