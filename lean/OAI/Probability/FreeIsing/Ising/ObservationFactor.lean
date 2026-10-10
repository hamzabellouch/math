import OAI.Probability.FreeIsing.Factors.ObservableFactorRecovery
import OAI.Probability.FreeIsing.Ising.ObservationLaw
import OAI.Probability.FreeIsing.Ising.ObservationRecovery

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ}

def field (beta : ℝ) (v : TreeVertex d) (t : ℝ≥0) (x : Paths d) : ℝ :=
  Real.artanh (posterior beta v t x)

theorem measurable_posterior_joint (beta : ℝ) (v : TreeVertex d) :
    Measurable (fun p : ℝ≥0 × Paths d => posterior beta v p.1 p.2) :=
  (stronglyMeasurable_joint_of_isStronglyProgressive
    (posterior_progressive beta v)).measurable

theorem measurable_field_joint (beta : ℝ) (v : TreeVertex d) :
    Measurable (fun p : ℝ≥0 × Paths d => field beta v p.1 p.2) := by
  have hm := measurable_posterior_joint beta v
  unfold field Real.artanh
  exact ((measurable_const.add hm).div (measurable_const.sub hm)).sqrt.log

private theorem measurable_tanh : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.measurable.div Real.continuous_cosh.measurable

theorem measurable_tanh_field_real_joint (beta : ℝ) (v : TreeVertex d) :
    Measurable (fun p : ℝ × Paths d => Real.tanh (field beta v p.1.toNNReal p.2)) := by
  have hmap : Measurable (fun p : ℝ × Paths d => (p.1.toNNReal, p.2)) :=
    measurable_real_toNNReal.prodMap measurable_id
  have hf : Measurable (fun p : ℝ × Paths d => field beta v p.1.toNNReal p.2) :=
    Measurable.comp (g := fun q : ℝ≥0 × Paths d => field beta v q.1 q.2)
      (f := fun p : ℝ × Paths d => (p.1.toNNReal, p.2))
      (measurable_field_joint beta v) hmap
  exact Measurable.comp (g := Real.tanh)
    (f := fun p : ℝ × Paths d => field beta v p.1.toNNReal p.2) measurable_tanh hf

theorem posterior_mem_Ioo_ae {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    ∀ᵐ x ∂observationLaw μ, posterior beta v t x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hm : Measurable (posterior beta v t) :=
    (measurable_infiniteGibbsSpinMean beta v).comp
      (Measurable.of_eval fun i => measurable_evaluation i t)
  apply (ae_map_iff measurable_uniformObservation.aemeasurable (hm measurableSet_Ioo)).mpr
  have hb := hμ.infiniteGibbsSpinMean_brownian_field_bound hbeta
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
    t v
  filter_upwards [hb] with q hq
  change infiniteGibbsSpinMean beta v
    (fun i => WienerSampler.sample (q.2 i) t + (t : ℝ) * spinSign (q.1 i)) ∈ _
  simpa only [add_comm] using hq.1

theorem tanh_field_eq_posterior_ae {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    (fun x => Real.tanh (field beta v t x)) =ᵐ[observationLaw μ] posterior beta v t := by
  filter_upwards [posterior_mem_Ioo_ae hμ hbeta v t] with x hx
  exact Real.tanh_artanh hx

def kernel (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : Kernel (Paths d) (Paths d) :=
  ObservableDisintegration.kernel (observationLaw μ) (innovationMap beta)

instance kernel_markov (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : IsMarkovKernel (kernel beta μ) := by
  unfold kernel
  infer_instance

def copies (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : Measure (Paths d × (Paths d × Paths d)) :=
  ((observationLaw μ).map (innovationMap beta)) ⊗ₘ
    ((kernel beta μ) ×ₖ (kernel beta μ))

instance copies_probability (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (copies beta μ) := by
  unfold copies
  infer_instance

theorem isFactorOfIID_of_root_field_zero {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d)
    (hInt : ∀ t, Integrable
      (fun p => (field beta o t p.2.1 - field beta o t p.2.2) ^ 2) (copies beta μ))
    (hzero : ∀ t, (∫ p, (field beta o t p.2.1 - field beta o t p.2.2) ^ 2
      ∂copies beta μ) = 0) :
    IsFactorOfIID d (Real.tanh beta) := by
  let E : Paths d → TreeVertex d → ℕ → ℝ := fun x v n => x v n
  have hE : Measurable E := Measurable.of_eval fun v =>
    Measurable.of_eval fun n => measurable_evaluation v n
  apply isFactorOfIID_of_stationary_innovation_observable
    WienerSampler.wienerMeasure (observationLaw μ) (innovationMap beta)
    (measurable_innovationMap beta) (map_innovationMap_observationLaw hμ)
    E hE (fun g => relabel g) (measurePreserving_observationLaw_relabel hμ)
    (fun _ _ => rfl) (innovationMap_relabel_ae hμ) o
    (IsingObservationRecovery.hasFreeIsingLaw_decode_observationLaw hμ)
    (field beta o) (fun n w => w o n)
    (measurable_tanh_field_real_joint beta o) hInt hzero
  intro n
  have hp := nnrealTimePrimitive_ae_eq_of_jointlyMeasurable
    (P := observationLaw μ)
    (measurable_tanh.comp (measurable_field_joint beta o))
    (measurable_posterior_joint beta o)
    (tanh_field_eq_posterior_ae hμ hbeta o) (n : ℝ≥0)
  filter_upwards [hp] with x hx
  change x o n = innovationMap beta x o n +
    nnrealTimePrimitive (fun t x => Real.tanh (field beta o t x)) n x
  rw [hx, innovationMap_apply]
  ring

end Problem367.IsingObservationFactor

end

end OAI
