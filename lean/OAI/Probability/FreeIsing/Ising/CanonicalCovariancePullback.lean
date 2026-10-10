import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse
import OAI.Probability.FreeIsing.Ising.MixedFiltering
import OAI.Probability.FreeIsing.Ising.ObservationPosteriorTransport

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.IsingObservationInnovation

theorem progressive_uniformObservation {d : ℕ}
    (hmB : ∀ t, Measurable (fun u => WienerSampler.sample u t))
    {H : ℝ≥0 → Paths d → ℝ} (hH : IsStronglyProgressive (filtration d) H) :
    IsStronglyProgressive
      (ArrayPosteriorStationarity.filtration (fun t u => WienerSampler.sample u t) hmB)
      (fun t q => H t (uniformObservation q)) := by
  intro t
  have hφ : Measurable[
      ArrayPosteriorStationarity.filtration (fun s u => WienerSampler.sample u s) hmB t,
      filtration d t] uniformObservation := by
    rw [← filtration_comap_uniformObservation d t hmB]
    exact comap_measurable _
  let : MeasurableSpace (IsingInnovation.State d ℝ) :=
    ArrayPosteriorStationarity.filtration (fun s u => WienerSampler.sample u s) hmB t
  let : MeasurableSpace (Paths d) := filtration d t
  exact (hH t).comp_measurable (measurable_id.prodMap hφ)

end Problem367.IsingObservationInnovation

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

theorem continuousRootCovariance_uniformObservation_progressive
    (hmB : ∀ t, Measurable (fun u => WienerSampler.sample u t))
    (hb : 0 ≤ beta) (v : TreeVertex d) :
    IsStronglyProgressive
      (ArrayPosteriorStationarity.filtration (fun t u => WienerSampler.sample u t) hmB)
      (fun t q => continuousRootCovariance hb v t (uniformObservation q)) :=
  progressive_uniformObservation hmB (continuousRootCovariance_progressive hb v)

theorem continuousRootCovariance_uniformObservation_stronglyAdapted
    (hmB : ∀ t, Measurable (fun u => WienerSampler.sample u t))
    (hb : 0 ≤ beta) (v : TreeVertex d) :
    StronglyAdapted
      (ArrayPosteriorStationarity.filtration (fun t u => WienerSampler.sample u t) hmB)
      (fun t q => continuousRootCovariance hb v t (uniformObservation q)) :=
  (continuousRootCovariance_uniformObservation_progressive hmB hb v).stronglyAdapted

theorem continuousRootCovariance_uniformObservation_abs_le_one
    (hb : 0 ≤ beta) (v : TreeVertex d) (t : ℝ≥0) (q : IsingInnovation.State d ℝ) :
    |continuousRootCovariance hb v t (uniformObservation q)| ≤ 1 :=
  continuousRootCovariance_abs_le_one hb v t (uniformObservation q)

theorem continuousRootCovariance_uniformObservation_continuous_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    ∀ᵐ q ∂μ.prod (labelMeasure d),
      Continuous (fun t => continuousRootCovariance hb v t (uniformObservation q)) :=
  (measurePreserving_uniformObservation μ).quasiMeasurePreserving.ae
    (continuousRootCovariance_continuous_ae hd hμ hb hcrit v)

theorem continuousRootCovariance_uniformObservation_eq_covariance_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    (fun q => continuousRootCovariance hb v t (uniformObservation q)) =ᵐ[
      μ.prod (labelMeasure d)]
      IsingInnovation.covariance beta (fun s u => WienerSampler.sample u s)
        (ConnectedHull.root d) v t := by
  exact (measurePreserving_uniformObservation μ).quasiMeasurePreserving.ae
    (continuousRootCovariance_eq_covariance_ae hd hμ hb hcrit v t)

end Problem367.IsingObservationFactor

end

end OAI
