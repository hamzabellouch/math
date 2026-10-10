import OAI.Probability.FreeIsing.Estimates.ArrayInnovationLaw
import OAI.Probability.FreeIsing.Ising.Innovation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingInnovation

private theorem spinArray_bound {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (v : TreeVertex d) :
    ∀ᵐ sigma ∂μ, |ArrayPosteriorStationarity.spinArray sigma v| ≤ (1 : ℝ≥0) := by
  apply Filter.Eventually.of_forall
  intro sigma
  cases hs : sigma v <;> norm_num [ArrayPosteriorStationarity.spinArray, spinSign, hs]

theorem map_innovation_array_eq_wiener_product {d : ℕ} {A : Type*}
    [MeasurableSpace A] {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a)) :
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map
      (fun q v t => innovation beta B v t q) =
      Measure.infinitePi (fun _ : TreeVertex d =>
        WienerSampler.wienerMeasure.map (fun f t => f t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact ArrayInnovationLaw.map_innovation_array_eq_infinitePi_reference
    μ (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
    ArrayPosteriorStationarity.measurable_spinArray (spinArray_bound μ)
    (posterior_progressive beta B hmB hcB)
    (fun v t => posterior_eq_condExp hμ ν hB hmB t v)
    WienerSampler.coordinate_isBrownianReal.toIsPreBrownianReal
    (fun t => (continuous_eval_const t).measurable)

theorem exists_continuous_innovation_array {d : ℕ} {A : Type*}
    [MeasurableSpace A] {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a)) :
    ∃ X : State d A → TreeVertex d → WienerSampler.Path,
      Measurable X ∧
      (∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
        ∀ v t, X q v t = innovation beta B v t q) ∧
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map X =
        Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure) ∧
      ∀ g : TreeAut d,
        ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
          X (ArrayPosteriorStationarity.plantedRelabel g q) = relabel g (X q) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Y, hYm, hYe, hYlaw⟩ :=
    ArrayInnovationLaw.exists_continuous_innovation_array_wiener_law
      μ (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB)
      ArrayPosteriorStationarity.measurable_spinArray (spinArray_bound μ)
      (posterior_progressive beta B hmB hcB)
      (fun v t => posterior_eq_condExp hμ ν hB hmB t v)
      (fun _ => Filter.Eventually.of_forall hcB)
  have heq : ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      ∀ v t, Y v q t = innovation beta B v t q := ae_all_iff.mpr hYe
  refine ⟨fun q v => Y v q, Measurable.of_eval hYm, heq, hYlaw, ?_⟩
  intro g
  have htrans := (ArrayPosteriorStationarity.measurePreserving_plantedRelabel
    hμ ν g).quasiMeasurePreserving.ae heq
  filter_upwards [heq, htrans, innovation_array_relabel_ae hμ ν hB hmB hcB g]
    with q hq hqg hg
  funext v
  apply ContinuousMap.ext
  intro t
  calc
    Y v (ArrayPosteriorStationarity.plantedRelabel g q) t =
        innovation beta B v t (ArrayPosteriorStationarity.plantedRelabel g q) := hqg v t
    _ = innovation beta B (g.toEquiv.symm v) t q := congrFun (congrFun hg v) t
    _ = Y (g.toEquiv.symm v) q t := (hq (g.toEquiv.symm v) t).symm

theorem map_uniformInnovation_eq_wiener_product {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    (μ.prod (labelMeasure d)).map (uniformInnovation beta) =
      Measure.infinitePi (fun _ : TreeVertex d =>
        WienerSampler.wienerMeasure.map (fun f t => f t)) := by
  exact map_innovation_array_eq_wiener_product hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun u => (WienerSampler.sample u).continuous)

theorem exists_continuous_uniformInnovation {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) :
    ∃ X : State d ℝ → TreeVertex d → WienerSampler.Path,
      Measurable X ∧
      (∀ᵐ q ∂μ.prod (labelMeasure d), ∀ v t, X q v t = uniformInnovation beta q v t) ∧
      (μ.prod (labelMeasure d)).map X =
        Measure.infinitePi (fun _ : TreeVertex d => WienerSampler.wienerMeasure) ∧
      ∀ g : TreeAut d, ∀ᵐ q ∂μ.prod (labelMeasure d),
        X (Prod.map (relabel g) (relabel g) q) = relabel g (X q) := by
  exact exists_continuous_innovation_array hμ uniform01
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
    (fun t => WienerSampler.measurable_sample_eval.comp
      (measurable_const.prodMk measurable_id))
    (fun u => (WienerSampler.sample u).continuous)

end Problem367.IsingInnovation

end

end OAI
