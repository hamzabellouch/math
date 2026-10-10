import OAI.Probability.FreeIsing.Posterior.PlantedBridgeInfinite
import OAI.Probability.FreeIsing.Posterior.PlantedSufficiency

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal

namespace Problem367.TerminalSufficiency

theorem comap_array_past_zero {ι Ω E : Type*} [MeasurableSpace E]
    (X : Ω → ℝ≥0 → ι → E) :
    MeasurableSpace.comap
      (fun ω i (s : Set.Iic (0 : ℝ≥0)) => X ω s i) inferInstance =
    MeasurableSpace.comap (fun ω i => X ω 0 i) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω i => X ω 0 i) inferInstance
    apply Measurable.comap_le
    have h : Measurable (fun ω i => X ω 0 i) := comap_measurable _
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    have hs : (s : ℝ≥0) = 0 := le_antisymm s.property bot_le
    simpa only [hs, Function.comp_def] using (measurable_pi_apply i).comp h
  · let : MeasurableSpace Ω := MeasurableSpace.comap
      (fun ω i (s : Set.Iic (0 : ℝ≥0)) => X ω s i) inferInstance
    apply Measurable.comap_le
    have h : Measurable (fun ω i (s : Set.Iic (0 : ℝ≥0)) => X ω s i) :=
      comap_measurable _
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply (⟨0, by simp⟩ : Set.Iic (0 : ℝ≥0))).comp
      ((measurable_pi_apply i).comp h)

theorem condExp_planted_array_past_eq_terminal_of_indep
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (ξ : Measure (ι → Ω))
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t))
    (signal : S → ι → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    {T : ℝ≥0} (hT : T ≠ 0)
    (hindep : IndepFun
      (fun q : S × (ι → Ω) =>
        (q.1, fun i => (T : ℝ) * signal q.1 i + B i T (q.2 i)))
      (fun q i (s : Set.Iic T) => brownianBridge (B i) T s (q.2 i))
      (ν.prod ξ)) :
    (ν.prod ξ)[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 i + B i s.1 (q.2 i)) inferInstance] =ᵐ[ν.prod ξ]
    (ν.prod ξ)[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i =>
          (T : ℝ) * signal q.1 i + B i T (q.2 i)) inferInstance] := by
  let Y : S × (ι → Ω) → ι → ℝ :=
    fun q i => (T : ℝ) * signal q.1 i + B i T (q.2 i)
  let R : S × (ι → Ω) → ι → Set.Iic T → ℝ :=
    fun q i s => brownianBridge (B i) T s (q.2 i)
  have hYm : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact ((((measurable_pi_apply i).comp hSignal).comp measurable_fst).const_mul _).add
      ((hmB i T).comp ((measurable_pi_apply i).comp measurable_snd))
  have hRm : Measurable R := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    exact ((hmB i s).comp ((measurable_pi_apply i).comp measurable_snd)).sub
      (((hmB i T).comp ((measurable_pi_apply i).comp measurable_snd)).const_mul _)
  have hInd : IndepFun (fun q : S × (ι → Ω) => (f q.1, Y q)) R (ν.prod ξ) := by
    have hm : Measurable (fun q : S × (ι → ℝ) => (f q.1, q.2)) :=
      (hf.comp measurable_fst).prodMk measurable_snd
    simpa only [Function.comp_def, id_eq] using hindep.comp hm measurable_id
  apply condExp_observation_eq_statistic (ν.prod ξ) (fun q => f q.1) Y R _
    (hf.comp measurable_fst) hYm hRm (hfint.comp_fst ξ) hInd
  rw [Problem367.comap_planted_vector_past_eq_terminal_bridges B signal hT]
  exact MeasurableSpace.comap_prodMk Y R

theorem condExp_planted_vector_past_eq_terminal
    {ι S Ω : Type*} [Fintype ι] [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    (signal : S → ι → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    (T : ℝ≥0) :
    (ν.prod (Measure.pi μ))[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 i + B i s.1 (q.2 i)) inferInstance]
        =ᵐ[ν.prod (Measure.pi μ)]
    (ν.prod (Measure.pi μ))[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i =>
          (T : ℝ) * signal q.1 i + B i T (q.2 i)) inferInstance] := by
  by_cases hT : T = 0
  · subst T
    rw [comap_array_past_zero
      (fun (q : S × (ι → Ω)) t i => (t : ℝ) * signal q.1 i + B i t (q.2 i))]
  have (index : ι) : IsProbabilityMeasure (μ index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  exact condExp_planted_array_past_eq_terminal_of_indep ν (Measure.pi μ) hmB signal f
    hSignal hf hfint hT
    (Problem367.planted_bridges_indep_signal_terminal ν μ hB hmB hSignal hT)

theorem condExp_planted_infinite_past_eq_terminal
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    (signal : S → ι → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    (T : ℝ≥0) :
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 i + B i s.1 (q.2 i)) inferInstance]
        =ᵐ[ν.prod (Measure.infinitePi μ)]
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => fun i =>
          (T : ℝ) * signal q.1 i + B i T (q.2 i)) inferInstance] := by
  by_cases hT : T = 0
  · subst T
    rw [comap_array_past_zero
      (fun (q : S × (ι → Ω)) t i => (t : ℝ) * signal q.1 i + B i t (q.2 i))]
  have (index : ι) : IsProbabilityMeasure (μ index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  exact condExp_planted_array_past_eq_terminal_of_indep ν (Measure.infinitePi μ)
    hmB signal f hSignal hf hfint hT
    (Problem367.planted_infinite_bridges_indep_signal_terminal ν μ hB hmB hSignal hT)

end Problem367.TerminalSufficiency

end

end OAI
