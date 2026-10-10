import OAI.Probability.FreeIsing.Brownian.Observation
import OAI.Probability.FreeIsing.Posterior.PlantedBridgeInfinite

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

def arrayNaturalFiltration {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t)) :
    Filtration ℝ≥0 mΩ where
  seq t := ⨆ i, Filtration.natural (X i) (fun t => (hm i t).stronglyMeasurable) t
  mono' _ _ hst := iSup_mono fun i => (Filtration.natural (X i)
    (fun t => (hm i t).stronglyMeasurable)).mono hst
  le' t := iSup_le fun i => (Filtration.natural (X i)
    (fun t => (hm i t).stronglyMeasurable)).le t

lemma arrayNaturalFiltration_eq_comap {ι Ω : Type*} [MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t)) (t : ℝ≥0) :
    arrayNaturalFiltration X hm t =
      MeasurableSpace.comap (fun ω i (s : Set.Iic t) => X i s ω) inferInstance := by
  simp only [arrayNaturalFiltration, MeasurableSpace.comap_process_pi,
    Filtration.natural_eq_comap]

lemma arrayNaturalFiltration_stronglyAdapted {ι Ω : Type*} [MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t)) (i : ι) :
    StronglyAdapted (arrayNaturalFiltration X hm) (X i) := by
  intro t
  exact (Filtration.stronglyAdapted_natural
    (fun t => (hm i t).stronglyMeasurable) t).mono (show
      Filtration.natural (X i) (fun t => (hm i t).stronglyMeasurable) t ≤
        ⨆ j, Filtration.natural (X j) (fun t => (hm j t).stronglyMeasurable) t from
      le_iSup (fun j : ι => Filtration.natural (X j)
        (fun t => (hm j t).stronglyMeasurable) t) i)

lemma arrayNaturalFiltration_le {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    (X : ι → ℝ≥0 → Ω → ℝ) (hm : ∀ i t, Measurable (X i t))
    {F : Filtration ℝ≥0 mΩ} (had : ∀ i, StronglyAdapted F (X i)) :
    arrayNaturalFiltration X hm ≤ F := by
  intro t
  exact iSup_le fun i => naturalFiltration_le_of_stronglyAdapted
    (fun t => (hm i t).stronglyMeasurable) (had i) t

def signalArrayFiltration {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (S × (ι → Ω))) :=
  Filtration.const ℝ≥0 (MeasurableSpace.comap Prod.fst inferInstance)
    measurable_fst.comap_le ⊔
    arrayNaturalFiltration (fun i t (q : S × (ι → Ω)) => B i t (q.2 i))
      (fun i t => (hmB i t).comp ((measurable_pi_apply i).comp measurable_snd))

lemma signalArrayFiltration_eq_comap {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) :
    signalArrayFiltration (S := S) B hmB t =
      MeasurableSpace.comap
        (fun q : S × (ι → Ω) => (q.1, fun i (s : Set.Iic t) => B i s (q.2 i)))
        inferInstance := by
  change MeasurableSpace.comap Prod.fst inferInstance ⊔
    arrayNaturalFiltration _ _ t = _
  rw [arrayNaturalFiltration_eq_comap]
  exact (MeasurableSpace.comap_prodMk Prod.fst
    (fun q : S × (ι → Ω) => fun i (s : Set.Iic t) => B i s (q.2 i))).symm

theorem planted_array_increments_indep_signal_past
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun
      (fun q : S × (ι → Ω) => fun i => B i t (q.2 i) - B i s (q.2 i))
      (fun q : S × (ι → Ω) => (q.1, fun i (u : Set.Iic s) => B i u (q.2 i)))
      (ν.prod (Measure.infinitePi μ)) := by
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hmPast (i : ι) : Measurable (fun ω (u : Set.Iic s) => B i u ω) :=
    Measurable.of_eval fun u => hmB i u
  have hmInc (i : ι) : Measurable (fun ω => B i t ω - B i s ω) :=
    (hmB i t).sub (hmB i s)
  have hind := indepFun_infinitePi_of_coordinate_indepFun μ hmPast hmInc
    (fun i => (preBrownian_increment_indep_past (hB i) hst).symm)
  exact (indepFun_prod_left_of_indepFun ν (Measure.infinitePi μ)
    (Measurable.of_eval fun i => (hmPast i).comp (measurable_pi_apply i))
    (Measurable.of_eval fun i => (hmInc i).comp (measurable_pi_apply i)) hind).symm

lemma planted_noise_coordinate_measurePreserving
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun q : S × (ι → Ω) => q.2 i)
      (ν.prod (Measure.infinitePi μ)) (μ i) := by
  refine ⟨(measurable_pi_apply i).comp measurable_snd, ?_⟩
  change Measure.map ((fun w : ι → Ω => w i) ∘ Prod.snd) _ = _
  rw [← Measure.map_map (measurable_pi_apply i) measurable_snd]
  simp only [Measure.map_snd_prod, measure_univ, one_smul]
  exact Measure.infinitePi_map_eval μ i

theorem preBrownian_martingale_signalArrayFiltration
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) (i : ι) :
    Martingale (fun t (q : S × (ι → Ω)) => B i t (q.2 i))
      (signalArrayFiltration B hmB) (ν.prod (Measure.infinitePi μ)) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := signalArrayFiltration (S := S) B hmB
  have hproj := planted_noise_coordinate_measurePreserving ν μ i
  have hint (t : ℝ≥0) : Integrable (fun q : S × (ι → Ω) => B i t (q.2 i)) P :=
    hproj.integrable_comp_of_integrable ((hB i).integrable_eval t)
  have had : StronglyAdapted F (fun t (q : S × (ι → Ω)) => B i t (q.2 i)) := by
    intro t
    exact (arrayNaturalFiltration_stronglyAdapted
      (fun j u (q : S × (ι → Ω)) => B j u (q.2 j))
      (fun j u => (hmB j u).comp ((measurable_pi_apply j).comp measurable_snd)) i t).mono
      le_sup_right
  apply martingale_of_conditional_increment_zero had hint
  intro s t hst
  have hind := (planted_array_increments_indep_signal_past ν μ hB hmB hst).comp
    (measurable_pi_apply i) measurable_id
  have hn := signalArrayFiltration_eq_comap (S := S) B hmB s
  have hcond : P[(fun q : S × (ι → Ω) => B i t (q.2 i) - B i s (q.2 i)) | F s] =ᵐ[P]
      fun _ => ∫ q : S × (ι → Ω), B i t (q.2 i) - B i s (q.2 i) ∂P := by
    change P[_ | signalArrayFiltration B hmB s] =ᵐ[P] _
    rw [hn]
    exact condExp_indep_eq
      (((hmB i t).sub (hmB i s)).comp hproj.measurable).comap_le
      (hn ▸ F.le s) (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hind
  have hzero : (∫ q : S × (ι → Ω), B i t (q.2 i) - B i s (q.2 i) ∂P) = 0 := by
    have hi := integral_map (μ := P) hproj.measurable.aemeasurable
      (((hmB i t).sub (hmB i s)).aestronglyMeasurable)
    rw [hproj.map_eq] at hi
    simp only [Pi.sub_apply] at hi
    rw [← hi, integral_sub ((hB i).integrable_eval t) ((hB i).integrable_eval s),
      (hB i).integral_eval, (hB i).integral_eval, sub_self]
  simpa only [hzero, Pi.sub_def] using hcond

def plantedArrayObservation {ι S Ω : Type*}
    (B : ι → ℝ≥0 → Ω → ℝ) (σ : S → ι → ℝ)
    (i : ι) (t : ℝ≥0) (q : S × (ι → Ω)) : ℝ :=
  B i t (q.2 i) + (t : ℝ) * σ q.1 i

lemma plantedArrayObservation_measurable {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι) (t : ℝ≥0) :
    Measurable (plantedArrayObservation B σ i t) :=
  ((hmB i t).comp ((measurable_pi_apply i).comp measurable_snd)).add
    ((((measurable_pi_apply i).comp hσ).comp measurable_fst).const_mul _)

def arrayObservationFiltration {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (σ : S → ι → ℝ) (hσ : Measurable σ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (S × (ι → Ω))) :=
  arrayNaturalFiltration (plantedArrayObservation B σ)
    (plantedArrayObservation_measurable hmB hσ)

lemma arrayObservationFiltration_le_signalArrayFiltration {ι S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (σ : S → ι → ℝ) (hσ : Measurable σ) :
    arrayObservationFiltration B hmB σ hσ ≤ signalArrayFiltration B hmB := by
  apply arrayNaturalFiltration_le
  intro i t
  have hnoise : StronglyMeasurable[signalArrayFiltration (S := S) B hmB t]
      (fun q : S × (ι → Ω) => B i t (q.2 i)) :=
    (arrayNaturalFiltration_stronglyAdapted
      (fun j u (q : S × (ι → Ω)) => B j u (q.2 j))
      (fun j u => (hmB j u).comp ((measurable_pi_apply j).comp measurable_snd)) i t).mono
      le_sup_right
  have hsignal : StronglyMeasurable[MeasurableSpace.comap
      (Prod.fst : S × (ι → Ω) → S) inferInstance]
      (fun q : S × (ι → Ω) => σ q.1 i) :=
    (((measurable_pi_apply i).comp hσ).comp (comap_measurable Prod.fst)).stronglyMeasurable
  exact hnoise.add (stronglyMeasurable_const.mul (hsignal.mono le_sup_left))

theorem preBrownian_array_observation_innovation_martingale
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    (hσint : Integrable (fun s => σ s i) ν)
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hmAd : StronglyAdapted (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t])
    (hAad : StronglyAdapted (arrayObservationFiltration B hmB σ hσ)
      (nnrealTimePrimitive m))
    (hInt : ∀ s t : ℝ≥0, s ≤ t →
      Integrable (fun p : ℝ × (S × (ι → Ω)) => m p.1.toNNReal p.2)
        ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod
          (ν.prod (Measure.infinitePi μ)))) :
    Martingale
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (arrayObservationFiltration B hmB σ hσ) (ν.prod (Measure.infinitePi μ)) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  exact compensated_observation_martingale_of_posterior_version
    (preBrownian_martingale_signalArrayFiltration ν μ hB hmB i)
    (arrayObservationFiltration_le_signalArrayFiltration B hmB σ hσ)
    (hσint.comp_fst (Measure.infinitePi μ))
    (arrayNaturalFiltration_stronglyAdapted (plantedArrayObservation B σ)
      (plantedArrayObservation_measurable hmB hσ) i)
    hmAd hposterior hAad hInt

end Problem367

end

end OAI
