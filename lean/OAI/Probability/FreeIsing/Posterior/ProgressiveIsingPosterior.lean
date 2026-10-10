import OAI.Probability.FreeIsing.Brownian.ArrayObservation
import OAI.Probability.FreeIsing.Brownian.PosteriorField

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance progressiveIsingPosteriorNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

def finiteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (y : TreeVertex d → ℝ) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta (connectedExhaustion v n))
    (fun (eta : connectedExhaustion v n → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩))
    ((connectedExhaustion v n).restrict y)

theorem continuous_finiteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsSpinMean beta v n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun w => continuous_apply w.1)

def infiniteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  max (-1) (min 1 (limUnder atTop (fun n => finiteGibbsSpinMean beta v n y)))

theorem measurable_infiniteGibbsSpinMean {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    Measurable (infiniteGibbsSpinMean beta v) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsSpinMean beta v n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsSpinMean beta v n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

theorem infiniteGibbsSpinMean_abs_le_one {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : |infiniteGibbsSpinMean beta v y| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v : TreeVertex d) :
    (fun p => infiniteGibbsSpinMean beta v (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hce (n : ℕ) := hμ.finiteObservation_condExp (connectedExhaustion v n)
    (connectedExhaustion_connected v n) t
    (fun eta => spinSign (eta ⟨v, mem_connectedExhaustion v n⟩))
  have hlim := tendsto_ae_condExp (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (ℱ := finiteObservationFiltration (connectedExhaustion v)
      (connectedExhaustion_monotone v) t) (fun p => spinSign (p.1 v))
  rw [finiteObservationFiltration_iSup (connectedExhaustion v)
    (connectedExhaustion_monotone v)
    (fun w => (eventually_mem_connectedExhaustion v w).exists) t] at hlim
  filter_upwards [ae_all_iff.mpr hce, hlim,
    posteriorMagnetization_abs_le_one (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v]
    with p hp hlim hb
  have hseq : Tendsto (fun n => finiteGibbsSpinMean beta v n (observation t p)) atTop
      (𝓝 (posteriorMagnetization (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) t v p)) := by
    convert hlim using 1
    · ext n
      exact (hp n).symm
    · rfl
  change max (-1) (min 1 (limUnder atTop _)) = _
  rw [hseq.limUnder_eq, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

theorem isStronglyProgressive_infiniteGibbsSpinMean
    {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) (beta : ℝ) (v : TreeVertex d)
    (X : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i, IsStronglyProgressive F (X i)) :
    IsStronglyProgressive F
      (fun t omega => infiniteGibbsSpinMean beta v (fun i => X i t omega)) := by
  intro t
  let : MeasurableSpace Ω := F t
  exact ((measurable_infiniteGibbsSpinMean beta v).comp
    (Measurable.of_eval (fun i => (hX i t).measurable))).stronglyMeasurable

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_eq_brownian_past
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) |
        MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
          inferInstance] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
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
  have heq := hμ.infiniteGibbsSpinMean_eq_posterior t v
  rw [← hT.map_eq] at heq
  have heq' := ae_of_ae_map hT.measurable.aemeasurable heq
  rw [hT.map_eq] at heq'
  filter_upwards [hpast, hpull, heq'] with p hpast hpull heq
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
  exact heq

theorem measurable_spinSign_array {ι : Type*} :
    Measurable (fun sigma : ι → IsingSpin => fun i => spinSign (sigma i)) := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  exact Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))

theorem HasFreeIsingLaw.exists_bounded_progressive_brownian_posterior
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (v : TreeVertex d) :
    let F := arrayObservationFiltration B hmB
      (fun sigma i => spinSign (sigma i)) measurable_spinSign_array
    ∃ m : ℝ≥0 → ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ,
      IsStronglyProgressive F m ∧ (∀ t p, |m t p| ≤ 1) ∧
      ∀ t, m t =ᵐ[μ.prod (Measure.infinitePi ν)]
        (μ.prod (Measure.infinitePi ν))[fun p => spinSign (p.1 v) | F t] := by
  dsimp only
  let X := plantedArrayObservation B
    (fun (sigma : TreeVertex d → IsingSpin) i => spinSign (sigma i))
  let hmX := plantedArrayObservation_measurable hmB
    (measurable_spinSign_array (ι := TreeVertex d))
  refine ⟨fun t p => infiniteGibbsSpinMean beta v (fun i => X i t p), ?_,
    fun t p => infiniteGibbsSpinMean_abs_le_one beta v _, ?_⟩
  · apply isStronglyProgressive_infiniteGibbsSpinMean
    intro i
    apply (arrayNaturalFiltration_stronglyAdapted X hmX i).isStronglyProgressive_of_continuous
    intro p
    exact (hcB i (p.2 i)).add (continuous_subtype_val.mul continuous_const)
  · intro t
    have heq := hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v
    simpa only [arrayObservationFiltration, arrayNaturalFiltration_eq_comap,
      X, plantedArrayObservation, add_comm] using heq

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_field_bound
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      let y := fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)
      infiniteGibbsSpinMean beta v y ∈ Set.Ioo (-1 : ℝ) 1 ∧
        |Real.artanh (infiniteGibbsSpinMean beta v y) - y v| ≤ (d : ℝ) * beta := by
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v,
    hμ.brownian_past_posterior_field_bound hbeta ν hB hmB t v] with p heq hb
  dsimp only
  rw [heq]
  exact hb

end Problem367

end

end OAI
