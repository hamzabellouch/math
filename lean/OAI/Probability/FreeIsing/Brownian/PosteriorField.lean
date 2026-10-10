import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Posterior.InfinitePosteriorField
import OAI.Probability.FreeIsing.Posterior.PlantedSufficiencyVector

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

open PlantedSymmetry

theorem condExp_comp_measurePreserving_comap
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : Ω → Ξ} (hT : MeasurePreserving T μ ν)
    {f : Ξ → ℝ} (_hf : StronglyMeasurable f) (hfi : Integrable f ν)
    {m : MeasurableSpace Ξ} (hm : m ≤ mΞ) :
    μ[f ∘ T | m.comap T] =ᵐ[μ] (ν[f | m]) ∘ T := by
  let : MeasurableSpace Ξ := mΞ
  exact condExp_comp_measurePreserving μ ν T hT m hm hfi

theorem brownian_array_eval_measurePreserving
    {ι Ω : Type*} [MeasurableSpace Ω] (ν : ι → Measure Ω)
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) :
    MeasurePreserving (fun ω i => B i t (ω i))
      (Measure.infinitePi ν) (gaussianNoiseLaw ι t) := by
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  refine ⟨Measurable.of_eval (fun i => (hmB i t).comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.infinitePi_map_pi ν (fun i => hmB i t)]
  congr 1
  funext i
  exact (hB i).hasLaw_eval t |>.map_eq

theorem HasFreeIsingLaw.brownian_past_posterior_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let m := ρ[fun p => spinSign (p.1 v) |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
        inferInstance]
    ∀ᵐ p ∂ρ, m p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (m p) - ((t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))| ≤
        (d : ℝ) * beta := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hspin : Measurable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) :=
    hsign.comp (measurable_pi_apply v)
  have hspini : Integrable (fun sigma : TreeVertex d → IsingSpin => spinSign (sigma v)) μ := by
    apply Integrable.of_bound hspin.aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro sigma
    cases hs : sigma v <;> norm_num [spinSign, hs]
  have hpull := condExp_comp_measurePreserving_comap hT
    (hspin.comp measurable_fst).stronglyMeasurable
    (integrable_plantedSpin (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) v)
    (observationSigma_le (TreeVertex d) t)
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i))
    (fun sigma => spinSign (sigma v))
    (Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))) hspin hspini t
  have hb := hμ.gaussian_posterior_field_bound hbeta t v
  rw [← hT.map_eq] at hb
  have hb' := ae_of_ae_map hT.measurable.aemeasurable hb
  rw [hT.map_eq] at hb'
  dsimp only
  filter_upwards [hpast, hpull, hb'] with p hpast hpull hb
  change _ = posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v (T p)
    at hpull
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  simp only [Function.comp_def, T, Prod.map_fst, id_eq] at hpull
  rw [hpast, hpull]
  exact hb

end Problem367

end

end OAI
