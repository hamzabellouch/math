import OAI.Probability.FreeIsing.Energy.SelectedCriticalFieldMoments
import OAI.Probability.FreeIsing.Stochastic.SelectedBrownianSufficiency

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

def selectedBrownianField {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) (ν : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ :=
  fun p => Real.artanh (selectedPosterior
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (fun s z (u : Set.Iic t) => (u.1 : ℝ) * spinSign s + B u.1 z) v r p)

theorem measurable_selectedBrownianField {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) (ν : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ} (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d) :
    Measurable (selectedBrownianField μ ν B t v r) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  apply ha.comp
  apply measurable_selectedPosterior
  apply Measurable.of_eval
  intro u
  exact ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
    ((hmB u.1).comp measurable_snd)

theorem selectedBrownianField_eq_gaussian_ae
    {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (hv : Function.Injective v)
    (r : TreeVertex d) :
    selectedBrownianField μ ν B t v r =ᵐ[μ.prod
      (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      fun p => selectedGaussianField μ t v r (p.1, fun i => B t (p.2 i)) := by
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let Q := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    fun p => (p.1, fun i => B t (p.2 i))
  have hT : MeasurePreserving T P Q :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t)
  have hs : Measurable (fun s : TreeVertex d → IsingSpin => spinSign (s r)) :=
    PlantedInformation.measurable_spinSign.comp (measurable_pi_apply r)
  have hsi : Integrable (fun s : TreeVertex d → IsingSpin => spinSign (s r)) μ := by
    apply Integrable.of_bound hs.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun s => by
      cases s r <;> simp [spinSign]
  have hSignal : Measurable (fun s : TreeVertex d → IsingSpin =>
      fun i => spinSign (s i)) :=
    Measurable.of_eval fun vertex =>
      PlantedInformation.measurable_spinSign.comp (measurable_pi_apply vertex)
  have hpast := TerminalSufficiency.condExp_planted_selected_past_eq_terminal
    μ (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
    v hv (fun s i => spinSign (s i)) (fun s => spinSign (s r))
    hSignal hs hsi t
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
      measurable_snd
  have hpull := condExp_comp_measurePreserving P Q T hT
    (selectedObservationField F v) (selectedObservationField_le hF v)
    (integrable_plantedSpin Q r)
  have hfield : (selectedObservationField F v).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 (v i)) + B t (p.2 (v i))) inferInstance := by
    rw [selectedObservationField, MeasurableSpace.comap_comp]
    rfl
  rw [hfield] at hpull
  filter_upwards [hpast, hpull] with p hp hq
  change Real.artanh _ = Real.artanh _
  apply congrArg Real.artanh
  exact hp.trans hq

theorem selectedBrownianField_identDistrib_gaussian
    {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (hv : Function.Injective v)
    (r : TreeVertex d) :
    IdentDistrib (selectedBrownianField μ ν B t v r) (selectedGaussianField μ t v r)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    fun p => (p.1, fun i => B t (p.2 i))
  have hT : MeasurePreserving T
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t)
  refine ⟨(measurable_selectedBrownianField μ ν hmB t v r).aemeasurable,
    (measurable_selectedGaussianField μ t v r).aemeasurable, ?_⟩
  rw [Measure.map_congr (selectedBrownianField_eq_gaussian_ae μ ν hB hmB t v hv r)]
  change Measure.map ((selectedGaussianField μ t v r) ∘ T) _ = _
  rw [← Measure.map_map (measurable_selectedGaussianField μ t v r) hT.measurable,
    hT.map_eq]

theorem selectedBrownianField_abs_moment_eq_gaussian
    {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (hv : Function.Injective v)
    (r : TreeVertex d) (p : ℕ) :
    (∫ q, |selectedBrownianField μ ν B t v r q| ^ p
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) =
    ∫ q, |selectedGaussianField μ t v r q| ^ p
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) :=
  ((selectedBrownianField_identDistrib_gaussian μ ν hB hmB t v hv r).comp
    (show Measurable (fun x : ℝ => |x| ^ p) by fun_prop)).integral_eq

theorem selectedBrownianField_tail_eq_gaussian
    {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (hv : Function.Injective v)
    (r : TreeVertex d) (a : ℝ) :
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      {q | a < |selectedBrownianField μ ν B t v r q|} =
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      {q | a < |selectedGaussianField μ t v r q|} := by
  exact (selectedBrownianField_identDistrib_gaussian μ ν hB hmB t v hv r).measure_mem_eq
    (measurableSet_lt measurable_const measurable_abs)

theorem HasFreeIsingLaw.integrable_selectedBrownianField_abs_pow
    {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (hv : Function.Injective v)
    (r : TreeVertex d) (hr : r ∈ Set.range v) (p : ℕ) :
    Integrable (fun q => |selectedBrownianField μ ν B t v r q| ^ p)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have h := (selectedBrownianField_identDistrib_gaussian μ ν hB hmB t v hv r).comp
    (show Measurable (fun x : ℝ => |x| ^ p) by fun_prop)
  exact h.integrable_iff.mpr
    (hμ.integrable_selectedGaussianField_abs_pow hb t v r hr p)

theorem HasFreeIsingLaw.brownianComponentField_critical_base_moments
    {d : ℕ} (hd : 3 ≤ d) {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d) (p : ℕ) (hp : p < 3) :
    (∫ q, |selectedBrownianField μ ν B t (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c) q| ^ p
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ≤
      Real.exp (criticalComponentBaseExponent d beta * (p : ℝ) ^ 2) *
        (t : ℝ) ^ ((p : ℝ) / 4) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  rw [selectedBrownianField_abs_moment_eq_gaussian μ ν hB hmB t _
    (componentIndexVertex_injective c)]
  exact hμ.gaussianComponentField_critical_base_moments hd hb hcritical t ht c p hp

end Problem367

end

end OAI
