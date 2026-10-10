import OAI.Probability.FreeIsing.Conditioning.ConstructedContinuousCopies
import OAI.Probability.FreeIsing.Conditioning.Copies

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ContinuousCopyBrownian

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

variable {ι : Type*}

theorem measurable_commonNoise_joinedFiltration (t : ℝ≥0) :
    Measurable[joinedFiltration (ι := ι) t]
      (fun q : Joint (ι := ι) => fun i => q.1 i t) := by
  change Measurable[pastSpace (ι := ι) t] _
  have hh : Measurable[pastSpace (ι := ι) t] (history (ι := ι) t) :=
    comap_measurable _
  let : MeasurableSpace (Joint (ι := ι)) := pastSpace (ι := ι) t
  apply Measurable.of_eval
  intro i
  have hm := (continuous_eval_const t).measurable.comp
    ((measurable_pi_apply i).comp (measurable_fst.comp hh))
  simpa only [Function.comp_def, history, stoppedArray, stoppedPath_apply, min_self] using hm

theorem indep_future_joinedFiltration [Countable ι]
    (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (eta : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel eta]
    (s : ℝ≥0)
    (hind : IndepFun (fun q : (ι → Path) × (ι → Path) =>
      (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta)) :
    Indep (MeasurableSpace.comap
      (fun q : Joint (ι := ι) => futureArray s q.1) inferInstance)
      (joinedFiltration s) (rho ⊗ₘ (eta ×ₖ eta)) := by
  exact (ContinuousNoiseSplit.indepFun_future_conditionalCopies s rho eta
    (stoppedArray s) (measurable_stoppedArray s) hind).symm

theorem indep_increment_joinedFiltration [Countable ι]
    (rho : Measure (ι → Path)) [IsProbabilityMeasure rho]
    (eta : Kernel (ι → Path) (ι → Path)) [IsMarkovKernel eta]
    {s t : ℝ≥0} (hst : s ≤ t)
    (hind : IndepFun (fun q : (ι → Path) × (ι → Path) =>
      (stoppedArray s q.1, stoppedArray s q.2))
      (fun q => futureArray s q.1) (rho ⊗ₘ eta)) :
    Indep (MeasurableSpace.comap
      (fun q : Joint (ι := ι) => fun i => q.1 i t - q.1 i s) inferInstance)
      (joinedFiltration s) (rho ⊗ₘ (eta ×ₖ eta)) := by
  have hcopy := ContinuousNoiseSplit.indepFun_future_conditionalCopies s rho eta
    (stoppedArray s) (measurable_stoppedArray s) hind
  have heval : Measurable (fun w : ι → Path => fun i => w i (t - s)) :=
    Measurable.of_eval fun i =>
      (continuous_eval_const (t - s)).measurable.comp (measurable_pi_apply i)
  have hi := hcopy.symm.comp heval measurable_id
  change IndepFun (fun q : Joint (ι := ι) => fun i => q.1 i t - q.1 i s)
    (fun q => (stoppedArray s q.1, (stoppedArray s q.2.1, stoppedArray s q.2.2)))
      (rho ⊗ₘ (eta ×ₖ eta))
  simpa only [Function.comp_def, id_eq, futureArray, futurePath_apply,
    add_tsub_cancel_of_le hst] using hi

end Problem367.ContinuousCopyBrownian

namespace Problem367.ConstructedContinuousCopies

open WienerSampler ContinuousObservationHistory ContinuousNoiseSplit

theorem exists_conditionalCopies_independentIncrements
    {ι Ω : Type*} [Countable ι] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (W Y : Ω → ι → Path)
    (hW : ∀ i t, Measurable[F t] (fun ω => W ω i t))
    (hY : ∀ i t, Measurable[F t] (fun ω => Y ω i t))
    (hB : ∀ i, IsPreBrownianReal (fun t ω => W ω i t) P)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω i => W ω i t - W ω i s) inferInstance) (F s) P) :
    ∃ (rho : Measure (ι → Path)) (eta : Kernel (ι → Path) (ι → Path)),
      IsProbabilityMeasure rho ∧ IsMarkovKernel eta ∧
      rho = P.map W ∧ rho ⊗ₘ eta = P.map (fun ω => (W ω, Y ω)) ∧
      (∀ i, IsBrownianReal
        (fun t (q : ContinuousCopyBrownian.Joint (ι := ι)) => q.1 i t)
        (rho ⊗ₘ (eta ×ₖ eta))) ∧
      (∀ i, Martingale
        (fun t (q : ContinuousCopyBrownian.Joint (ι := ι)) => q.1 i t)
        ContinuousCopyBrownian.joinedFiltration (rho ⊗ₘ (eta ×ₖ eta))) ∧
      (∀ s t, s ≤ t → Indep
        (MeasurableSpace.comap
          (fun q : ContinuousCopyBrownian.Joint (ι := ι) =>
            fun i => q.1 i t - q.1 i s) inferInstance)
        (ContinuousCopyBrownian.joinedFiltration s) (rho ⊗ₘ (eta ×ₖ eta))) ∧
      MeasurePreserving (Prod.map id Prod.fst : ContinuousCopyBrownian.Joint (ι := ι) → _)
        (rho ⊗ₘ (eta ×ₖ eta)) (P.map (fun ω => (W ω, Y ω))) ∧
      MeasurePreserving (Prod.map id Prod.snd : ContinuousCopyBrownian.Joint (ι := ι) → _)
        (rho ⊗ₘ (eta ×ₖ eta)) (P.map (fun ω => (W ω, Y ω))) := by
  obtain ⟨rho, eta, hrhop, hetap, hrho, hjoint, hBc, hMc⟩ :=
    exists_compatible_conditionalCopies P F W Y hW hY hB hind
  let : IsProbabilityMeasure rho := hrhop
  let : IsMarkovKernel eta := hetap
  refine ⟨rho, eta, hrhop, hetap, hrho, hjoint, hBc, hMc, ?_, ?_, ?_⟩
  · intro s t hst
    apply ContinuousCopyBrownian.indep_increment_joinedFiltration rho eta hst
    rw [hjoint]
    have hWm : Measurable W := Measurable.of_eval fun i =>
      measurable_path_of_eval (fun u => (hW i u).mono (F.le u) le_rfl)
    have hYm : Measurable Y := Measurable.of_eval fun i =>
      measurable_path_of_eval (fun u => (hY i u).mono (F.le u) le_rfl)
    apply ConstructedConditionalCopies.indepFun_map_of_comp (hWm.prodMk hYm)
      (((measurable_stoppedArray s).comp measurable_fst).prodMk
        ((measurable_stoppedArray s).comp measurable_snd))
      ((measurable_futureArray s).comp measurable_fst)
    exact indepFun_continuous_future P F W Y hW hY hind s
  · rw [← hjoint]
    exact measurePreserving_conditionalCopy_fst rho eta
  · rw [← hjoint]
    exact measurePreserving_conditionalCopy_snd rho eta

end Problem367.ConstructedContinuousCopies

end

end OAI
