import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Posterior.PlantedSufficiencyVector

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.TerminalSufficiency

theorem condExp_planted_selected_past_eq_terminal
    {ι κ S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : κ → Measure Ω) [IsProbabilityMeasure ν]
    {B : κ → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    (v : ι → κ) (hv : Function.Injective v)
    (signal : S → κ → ℝ) (f : S → ℝ)
    (hSignal : Measurable signal) (hf : Measurable f) (hfint : Integrable f ν)
    (T : ℝ≥0) :
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (κ → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (κ → Ω) => fun i (s : Set.Iic T) =>
          (s.1 : ℝ) * signal q.1 (v i) + B (v i) s.1 (q.2 (v i))) inferInstance]
        =ᵐ[ν.prod (Measure.infinitePi μ)]
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (κ → Ω) => f q.1) |
      MeasurableSpace.comap
        (fun q : S × (κ → Ω) => fun i =>
          (T : ℝ) * signal q.1 (v i) + B (v i) T (q.2 (v i))) inferInstance] := by
  have (i : κ) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let R : S × (κ → Ω) → S × (ι → Ω) :=
    Prod.map id (fun ω i => ω (v i))
  have hselect : MeasurePreserving (fun ω : κ → Ω => fun i => ω (v i))
      (Measure.infinitePi μ) (Measure.infinitePi (fun i => μ (v i))) :=
    ⟨Measurable.of_eval (fun i => measurable_pi_apply (v i)),
      Measure.map_infinitePi_infinitePi_of_inj hv⟩
  have hR : MeasurePreserving R (ν.prod (Measure.infinitePi μ))
      (ν.prod (Measure.infinitePi (fun i => μ (v i)))) :=
    (MeasurePreserving.id ν).prod hselect
  let ambient : MeasurableSpace (S × (ι → Ω)) := inferInstance
  let P : MeasurableSpace (S × (ι → Ω)) := MeasurableSpace.comap
    (fun q : S × (ι → Ω) => fun i (s : Set.Iic T) =>
      (s.1 : ℝ) * signal q.1 (v i) + B (v i) s.1 (q.2 i)) inferInstance
  let Q : MeasurableSpace (S × (ι → Ω)) := MeasurableSpace.comap
    (fun q : S × (ι → Ω) => fun i =>
      (T : ℝ) * signal q.1 (v i) + B (v i) T (q.2 i)) inferInstance
  let : MeasurableSpace (S × (ι → Ω)) := ambient
  have hP : P ≤ (inferInstance : MeasurableSpace (S × (ι → Ω))) := by
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro s
    exact (measurable_const.mul
      (((measurable_pi_apply (v i)).comp hSignal).comp measurable_fst)).add
      ((hmB (v i) s.1).comp ((measurable_pi_apply i).comp measurable_snd))
  have hQ : Q ≤ (inferInstance : MeasurableSpace (S × (ι → Ω))) := by
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    exact (measurable_const.mul
      (((measurable_pi_apply (v i)).comp hSignal).comp measurable_fst)).add
      ((hmB (v i) T).comp ((measurable_pi_apply i).comp measurable_snd))
  have hf' : Integrable (fun q : S × (ι → Ω) => f q.1)
      (ν.prod (Measure.infinitePi (fun i => μ (v i)))) := hfint.comp_fst _
  have hPast := Problem367.condExp_comp_measurePreserving
    (ν.prod (Measure.infinitePi μ))
    (ν.prod (Measure.infinitePi (fun i => μ (v i)))) R hR P hP hf'
  have hTerm := Problem367.condExp_comp_measurePreserving
    (ν.prod (Measure.infinitePi μ))
    (ν.prod (Measure.infinitePi (fun i => μ (v i)))) R hR Q hQ hf'
  have hCore := condExp_planted_infinite_past_eq_terminal ν (fun i => μ (v i))
    (fun i => hB (v i)) (fun i t => hmB (v i) t)
    (fun x i => signal x (v i)) f
    (Measurable.of_eval (fun i => (measurable_pi_apply (v i)).comp hSignal))
    hf hfint T
  have hPull := hR.quasiMeasurePreserving.ae_eq_comp hCore
  simp only [P, Q, MeasurableSpace.comap_comp] at hPast hTerm
  filter_upwards [hPast, hTerm, hPull] with q hp ht hc
  exact hp.trans (hc.trans ht.symm)

end Problem367.TerminalSufficiency

end

end OAI
