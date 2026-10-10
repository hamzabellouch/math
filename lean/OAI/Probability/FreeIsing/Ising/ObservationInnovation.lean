import OAI.Probability.FreeIsing.Ising.InnovationLaw
import OAI.Probability.FreeIsing.Trees.InnovationPathMap

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationInnovation

abbrev Paths (d : ℕ) := TreeVertex d → WienerSampler.Path

def evaluation {d : ℕ} (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) : ℝ := x v t

theorem measurable_evaluation {d : ℕ} (v : TreeVertex d) (t : ℝ≥0) :
    Measurable (evaluation v t) :=
  (continuous_eval_const t).measurable.comp (measurable_pi_apply v)

def filtration (d : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Paths d)) :=
  arrayNaturalFiltration evaluation measurable_evaluation

def posterior {d : ℕ} (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) : ℝ :=
  infiniteGibbsSpinMean beta v (fun i => x i t)

theorem posterior_progressive {d : ℕ} (beta : ℝ) (v : TreeVertex d) :
    IsStronglyProgressive (filtration d) (posterior beta v) := by
  apply isStronglyProgressive_infiniteGibbsSpinMean
  intro i
  apply (arrayNaturalFiltration_stronglyAdapted evaluation measurable_evaluation i).isStronglyProgressive_of_continuous
  intro x
  exact (x i).continuous

theorem posterior_norm_le_one {d : ℕ} (beta : ℝ) (v : TreeVertex d)
    (t : ℝ≥0) (x : Paths d) : ‖posterior beta v t x‖ ≤ (1 : ℝ≥0) :=
  infiniteGibbsSpinMean_abs_le_one beta v _

def innovationMap {d : ℕ} (beta : ℝ) (x : Paths d) : Paths d := fun v =>
  innovationPath (fun x : Paths d => x v) (posterior beta v)
    (posterior_progressive beta v) (posterior_norm_le_one beta v) x

@[simp] theorem innovationMap_apply {d : ℕ} (beta : ℝ) (x : Paths d)
    (v : TreeVertex d) (t : ℝ≥0) :
    innovationMap beta x v t = x v t - nnrealTimePrimitive (posterior beta v) t x := rfl

theorem measurable_innovationMap {d : ℕ} (beta : ℝ) :
    Measurable (innovationMap (d := d) beta) :=
  measurable_innovationPath_array (posterior_progressive beta)
    (posterior_norm_le_one beta) measurable_id

@[simp] theorem innovationMap_zero {d : ℕ} (beta : ℝ) (x : Paths d)
    (v : TreeVertex d) : innovationMap beta x v 0 = x v 0 := by
  simp [innovationMap, nnrealTimePrimitive]

theorem innovationMap_causal {d : ℕ} (beta : ℝ) {T : ℝ≥0} {x y : Paths d}
    (hpast : ∀ v s, s ≤ T → x v s = y v s) :
    ∀ v s, s ≤ T → innovationMap beta x v s = innovationMap beta y v s := by
  apply innovationPath_array_causal (posterior_progressive beta)
    (posterior_norm_le_one beta) _ hpast
  intro T x y hxy v s hs
  unfold posterior
  congr 1
  funext i
  exact hxy i s hs

def uniformObservation {d : ℕ} (q : IsingInnovation.State d ℝ) : Paths d := fun v =>
  ⟨fun t => WienerSampler.sample (q.2 v) t + (t : ℝ) * spinSign (q.1 v),
    (WienerSampler.sample (q.2 v)).continuous.add
      (NNReal.continuous_coe.mul continuous_const)⟩

theorem measurable_uniformObservation {d : ℕ} :
    Measurable (uniformObservation (d := d)) := by
  apply Measurable.of_eval
  intro v
  apply WienerSampler.measurable_path_of_eval
  intro t
  have hsign : Measurable spinSign := by intro s hs; trivial
  exact ((continuous_eval_const t).measurable.comp
    (WienerSampler.measurable_sample.comp ((measurable_pi_apply v).comp measurable_snd))).add
    ((hsign.comp ((measurable_pi_apply v).comp measurable_fst)).const_mul (t : ℝ))

@[simp] theorem innovationMap_uniformObservation {d : ℕ} (beta : ℝ)
    (q : IsingInnovation.State d ℝ) (v : TreeVertex d) (t : ℝ≥0) :
    innovationMap beta (uniformObservation q) v t =
      IsingInnovation.uniformInnovation beta q v t := rfl

@[simp] theorem uniformObservation_relabel {d : ℕ} (g : TreeAut d)
    (q : IsingInnovation.State d ℝ) :
    uniformObservation (Prod.map (relabel g) (relabel g) q) =
      relabel g (uniformObservation q) := rfl

def observationLaw {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin)) : Measure (Paths d) :=
  (μ.prod (labelMeasure d)).map uniformObservation

theorem map_innovationMap_observationLaw {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    (observationLaw μ).map (innovationMap beta) =
      Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure) := by
  obtain ⟨X, hXm, hXe, hXlaw, _⟩ := IsingInnovation.exists_continuous_uniformInnovation hμ
  rw [observationLaw, Measure.map_map (measurable_innovationMap beta)
    measurable_uniformObservation]
  apply (Measure.map_congr ?_).trans hXlaw
  filter_upwards [hXe] with q hq
  funext v
  apply ContinuousMap.ext
  intro t
  exact (hq v t).symm

theorem innovationMap_relabel_ae {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    ∀ᵐ x ∂observationLaw μ,
      innovationMap beta (relabel g x) = relabel g (innovationMap beta x) := by
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun
      ((measurable_innovationMap beta).comp (measurable_relabel g))
      ((measurable_relabel g).comp (measurable_innovationMap beta)))).mpr
  filter_upwards [(IsingInnovation.uniformInnovation_properties hμ).2.2 g] with q hq
  change innovationMap beta (relabel g (uniformObservation q)) =
    relabel g (innovationMap beta (uniformObservation q))
  rw [← uniformObservation_relabel]
  funext v
  apply ContinuousMap.ext
  intro t
  exact congrFun (congrFun hq v) t

end Problem367.IsingObservationInnovation

end

end OAI
