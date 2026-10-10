import OAI.Probability.FreeIsing.Brownian.ArrayInnovation
import OAI.Probability.FreeIsing.Posterior.ArrayPosteriorStationarity
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior
import OAI.Probability.FreeIsing.Stochastic.WienerSampler

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

abbrev State (d : ℕ) (A : Type*) :=
  (TreeVertex d → IsingSpin) × (TreeVertex d → A)

def posterior {d : ℕ} {A : Type*} (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v : TreeVertex d) (t : ℝ≥0) (q : State d A) : ℝ :=
  infiniteGibbsSpinMean beta v
    (fun i => plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray i t q)

def innovation {d : ℕ} {A : Type*} (beta : ℝ) (B : ℝ≥0 → A → ℝ)
    (v : TreeVertex d) (t : ℝ≥0) (q : State d A) : ℝ :=
  plantedArrayObservation (fun _ : TreeVertex d => B)
      ArrayPosteriorStationarity.spinArray v t q -
    nnrealTimePrimitive (posterior beta B v) t q

theorem posterior_abs_le_one {d : ℕ} {A : Type*}
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (v : TreeVertex d) (t : ℝ≥0) (q : State d A) :
    |posterior beta B v t q| ≤ 1 :=
  infiniteGibbsSpinMean_abs_le_one beta v _

theorem posterior_progressive {d : ℕ} {A : Type*} [MeasurableSpace A]
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) (v : TreeVertex d) :
    IsStronglyProgressive (ArrayPosteriorStationarity.filtration B hmB)
      (posterior beta B v) := by
  apply isStronglyProgressive_infiniteGibbsSpinMean
  intro i
  apply (arrayNaturalFiltration_stronglyAdapted
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
    (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray) i).isStronglyProgressive_of_continuous
  intro q
  exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)

theorem measurable_posterior_joint {d : ℕ} {A : Type*} [MeasurableSpace A]
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) (v : TreeVertex d) :
    Measurable (fun p : ℝ≥0 × State d A => posterior beta B v p.1 p.2) := by
  apply (measurable_infiniteGibbsSpinMean beta v).comp
  apply Measurable.of_eval
  intro i
  apply StronglyMeasurable.measurable
  change StronglyMeasurable (Function.uncurry
    (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray i))
  apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  · intro q
    exact (hcB (q.2 i)).add (continuous_subtype_val.mul continuous_const)
  · intro t
    exact (plantedArrayObservation_measurable (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray i t).stronglyMeasurable

theorem posterior_eq_condExp {d : ℕ} {A : Type*} [MeasurableSpace A]
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (t : ℝ≥0) (v : TreeVertex d) :
    posterior beta B v t =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      ArrayPosteriorStationarity.posterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) B hmB t v := by
  have heq := hμ.infiniteGibbsSpinMean_eq_brownian_past
    (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t v
  have hF : ArrayPosteriorStationarity.filtration (d := d) B hmB t =
      MeasurableSpace.comap
        (fun q : State d A => fun i (s : Set.Iic t) =>
          (s.1 : ℝ) * spinSign (q.1 i) + B s.1 (q.2 i)) inferInstance := by
    change arrayNaturalFiltration
      (plantedArrayObservation (fun _ : TreeVertex d => B) ArrayPosteriorStationarity.spinArray)
      (plantedArrayObservation_measurable (fun _ => hmB)
        ArrayPosteriorStationarity.measurable_spinArray) t = _
    rw [arrayNaturalFiltration_eq_comap]
    congr 1
    funext q i s
    exact add_comm _ _
  have hp : posterior beta B v t =
      (fun q : State d A => infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (q.1 i) + B t (q.2 i))) := by
    funext q
    unfold posterior
    congr 1
    funext i
    exact add_comm _ _
  rw [hp]
  unfold ArrayPosteriorStationarity.posterior
  rw [hF]
  exact heq

theorem isBrownianReal_innovation {d : ℕ} {A : Type*} [MeasurableSpace A]
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    IsBrownianReal (innovation beta B v)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  refine brownian_array_innovation_of_progressive_posterior
    μ (fun _ : TreeVertex d => ν)
    (fun _ => ⟨hB, Filter.Eventually.of_forall hcB⟩)
    (fun _ => hmB) ArrayPosteriorStationarity.measurable_spinArray v
    (C := 1) ?_ (posterior_progressive beta B hmB hcB v) ?_
  · apply Filter.Eventually.of_forall
    intro q
    cases hq : q v <;> norm_num [ArrayPosteriorStationarity.spinArray, spinSign, hq]
  · intro t
    exact posterior_eq_condExp hμ ν hB hmB t v

theorem measurable_innovation_array {d : ℕ} {A : Type*} [MeasurableSpace A]
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a)) :
    Measurable (fun q : State d A => fun v t => innovation beta B v t q) := by
  apply Measurable.of_eval
  intro v
  apply Measurable.of_eval
  intro t
  exact (plantedArrayObservation_measurable (fun _ => hmB)
    ArrayPosteriorStationarity.measurable_spinArray v t).sub
    (((stronglyAdapted_nnrealTimePrimitive (posterior_progressive beta B hmB hcB v) t).mono
      (ArrayPosteriorStationarity.filtration B hmB |>.le t)).measurable)

theorem innovation_array_relabel_ae {d : ℕ} {A : Type*} [MeasurableSpace A]
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (g : TreeAut d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      (fun v t => innovation beta B v t (ArrayPosteriorStationarity.plantedRelabel g q)) =
        relabel g (fun v t => innovation beta B v t q) := by
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  exact ArrayPosteriorStationarity.innovation_array_relabel_ae hμ ν B hmB
    (fun v => measurable_posterior_joint beta B hmB hcB v)
    (fun t v => posterior_eq_condExp hμ ν hB hmB t v) g

def uniformInnovation {d : ℕ} (beta : ℝ) :
    State d ℝ → TreeVertex d → ℝ≥0 → ℝ :=
  fun q v t => innovation beta (fun r u => WienerSampler.sample u r) v t q

theorem uniformInnovation_properties {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    Measurable (uniformInnovation (d := d) beta) ∧
    (∀ v : TreeVertex d,
      IsBrownianReal (fun t q => uniformInnovation beta q v t) (μ.prod (labelMeasure d))) ∧
    (∀ g : TreeAut d, ∀ᵐ q ∂μ.prod (labelMeasure d),
      uniformInnovation beta (Prod.map (relabel g) (relabel g) q) =
        relabel g (uniformInnovation beta q)) := by
  have hmB (t : ℝ≥0) : Measurable (fun u => WienerSampler.sample u t) :=
    WienerSampler.measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  have hcB (u : ℝ) : Continuous (fun t => WienerSampler.sample u t) :=
    (WienerSampler.sample u).continuous
  refine ⟨measurable_innovation_array beta _ hmB hcB, ?_, ?_⟩
  · intro v
    exact isBrownianReal_innovation hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB hcB v
  · intro g
    exact innovation_array_relabel_ae hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB hcB g

end Problem367.IsingInnovation

end

end OAI
