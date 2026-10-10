import OAI.Probability.FreeIsing.Estimates.FilteredFutureIndependence
import OAI.Probability.FreeIsing.Ising.InnovationLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]
  {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
  (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
  (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))

private theorem spin_bound (v : TreeVertex d) :
    ∀ᵐ sigma ∂μ, |ArrayPosteriorStationarity.spinArray sigma v| ≤ (1 : ℝ≥0) := by
  apply Filter.Eventually.of_forall
  intro sigma
  cases hs : sigma v <;> norm_num [ArrayPosteriorStationarity.spinArray, spinSign, hs]

include hμ hB hcB

theorem innovation_martingale (v : TreeVertex d) :
    Martingale (innovation beta B v) (ArrayPosteriorStationarity.filtration B hmB)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  exact preBrownian_array_innovation_martingale_of_progressive_posterior
    μ (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
    ArrayPosteriorStationarity.measurable_spinArray v (spin_bound v)
    (posterior_progressive beta B hmB hcB v)
    (fun t => posterior_eq_condExp hμ ν hB hmB t v)

theorem innovation_increment_law_and_indep
    {E : Type*} [mE : MeasurableSpace E] {Y : State d A → E}
    (s t : ℝ≥0) (hst : s ≤ t)
    (hY : Measurable[ArrayPosteriorStationarity.filtration B hmB s] Y) :
    HasLaw (fun q v => innovation beta B v t q - innovation beta B v s q)
      (Measure.infinitePi (fun _ : TreeVertex d => gaussianReal 0 (t - s)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ∧
    iIndepFun (fun v q => innovation beta B v t q - innovation beta B v s q)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) ∧
    IndepFun (fun q v => innovation beta B v t q - innovation beta B v s q) Y
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply ConditionalGaussianVector.infinite_product_gaussian_law_and_indep_of_condExp_linear_character
    (ArrayPosteriorStationarity.filtration B hmB |>.le s) _
    (fun _ : TreeVertex d => t - s) _ hY
  · apply Measurable.of_eval
    intro v
    exact ((innovation_martingale hμ ν hB hmB hcB v).stronglyMeasurable t).measurable.mono
      (ArrayPosteriorStationarity.filtration B hmB |>.le t) le_rfl |>.sub
        (((innovation_martingale hμ ν hB hmB hcB v).stronglyMeasurable s).measurable.mono
          (ArrayPosteriorStationarity.filtration B hmB |>.le s) le_rfl)
  · intro I a
    have h := ArrayInnovationLaw.conditional_weighted_character μ
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray (fun v => spin_bound v)
      (posterior_progressive beta B hmB hcB)
      (fun v t => posterior_eq_condExp hμ ν hB hmB t v) I s t hst a
    have heq : ConditionalCharacteristic.character
        (fun q => ∑ i : I, a i * (innovation beta B i.1 t q - innovation beta B i.1 s q)) 1 =
        (fun q => Complex.exp (((∑ i : I, a i *
          (innovation beta B i.1 t q - innovation beta B i.1 s q) : ℝ) : ℂ) * Complex.I)) := by
      funext q
      simp [ConditionalCharacteristic.character]
    change (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[
      ConditionalCharacteristic.character
        (fun q => ∑ i : I, a i * (innovation beta B i.1 t q - innovation beta B i.1 s q)) 1 |
        ArrayPosteriorStationarity.filtration B hmB s] =ᵐ[_] _ at h
    rw [heq] at h
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using h

theorem innovation_increment_indep_filtration (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun q v => innovation beta B v t q - innovation beta B v s q) inferInstance)
      (ArrayPosteriorStationarity.filtration B hmB s)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := (innovation_increment_law_and_indep hμ ν hB hmB hcB
    (mE := ArrayPosteriorStationarity.filtration B hmB s)
    (Y := id) s t hst measurable_id).2.2
  change Indep _ ((ArrayPosteriorStationarity.filtration B hmB s).comap id) _ at h
  simpa only [MeasurableSpace.comap_id] using h

theorem innovation_future_indep_filtration (s : ℝ≥0) :
    Indep (ArrayPosteriorStationarity.filtration B hmB s)
      (MeasurableSpace.comap
        (fun q (t : Set.Ici s) v => innovation beta B v t.val q - innovation beta B v s q)
        inferInstance)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply FilteredFutureIndependence.indep_future
    (X := fun t q v => innovation beta B v t q)
  · intro t
    let : MeasurableSpace (State d A) := ArrayPosteriorStationarity.filtration B hmB t
    exact Measurable.of_eval (fun v =>
      (innovation_martingale hμ ν hB hmB hcB v).stronglyAdapted.adapted t)
  · exact innovation_increment_indep_filtration hμ ν hB hmB hcB

theorem innovation_strict_future_indep
    {E : Type*} [MeasurableSpace E] {Y : State d A → E}
    (s : ℝ≥0)
    (hY : Measurable[ArrayPosteriorStationarity.filtration B hmB s] Y) :
    IndepFun Y
      (fun q (t : Set.Ioi s) v => innovation beta B v t.val q - innovation beta B v s q)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  apply FilteredFutureIndependence.indepFun_strict_future
    (X := fun t q v => innovation beta B v t q) _
    (innovation_increment_indep_filtration hμ ν hB hmB hcB) s hY
  intro t
  let : MeasurableSpace (State d A) := ArrayPosteriorStationarity.filtration B hmB t
  exact Measurable.of_eval (fun v =>
    (innovation_martingale hμ ν hB hmB hcB v).stronglyAdapted.adapted t)

omit hμ hB hcB in

def uniformObservationFiltration (d : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (State d ℝ)) :=
  ArrayPosteriorStationarity.filtration
    (fun t u => WienerSampler.sample u t)
    (fun _t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))

omit hB hmB hcB ν in

theorem uniformInnovation_future_indep_filtration (s : ℝ≥0) :
    Indep (uniformObservationFiltration d s)
      (MeasurableSpace.comap
        (fun q (t : Set.Ici s) v => uniformInnovation beta q v t.val -
          uniformInnovation beta q v s) inferInstance)
      (μ.prod (labelMeasure d)) := by
  exact innovation_future_indep_filtration hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun u => (WienerSampler.sample u).continuous) s

end Problem367.IsingInnovation

end

end OAI
