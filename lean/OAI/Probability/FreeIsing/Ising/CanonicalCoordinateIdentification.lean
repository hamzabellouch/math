import OAI.Probability.FreeIsing.Brownian.CoefficientApproximationIdentification
import OAI.Probability.FreeIsing.Brownian.IntegralTransport
import OAI.Probability.FreeIsing.Ising.CanonicalCovariancePullback
import OAI.Probability.FreeIsing.Ising.CoordinateCompletion
import OAI.Probability.FreeIsing.Ising.ObservationIndependence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem finiteCovariance_tendsto_version_timeMeanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (T : ℝ≥0)
    {H : ℝ≥0 → State d A → ℝ}
    (hver : ∀ t, H t =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      covariance beta B v u t) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..(T : ℝ), ∫ q,
      (finiteCovariance beta B v u n t.toNNReal q - H t.toNNReal q) ^ 2
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let τ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  have heq (n : ℕ) :
      (∫ t in (0 : ℝ)..(T : ℝ), ∫ q,
        (finiteCovariance beta B v u n t.toNNReal q - H t.toNNReal q) ^ 2 ∂P) =
      ∫ p : ℝ × State d A,
        (finiteCovariance beta B v u n p.1.toNNReal p.2 -
          covariance beta B v u p.1.toNNReal p.2) ^ 2 ∂τ.prod P := by
    calc
      _ = ∫ t in (0 : ℝ)..(T : ℝ), ∫ q,
          (finiteCovariance beta B v u n t.toNNReal q -
            covariance beta B v u t.toNNReal q) ^ 2 ∂P := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply integral_congr_ae
        filter_upwards [hver t.toNNReal] with q hq
        rw [hq]
      _ = _ := interval_integral_eq_timeSpace T
        ((memLp_finiteCovariance_time beta B hmB hcB P τ v u n).sub
          (memLp_covariance_time beta B hmB hcB P τ v u)).integrable_sq
  exact (finiteCovariance_tendsto_timeMeanSquare hμ ν hB hmB hcB v u T).congr'
    (Eventually.of_forall fun n => (heq n).symm)

end Problem367.IsingInnovation

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

theorem canonical_covariance_coordinate_integral_eq_pullback
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (u : TreeVertex d) (T : ℝ≥0)
    {X : ℕ → IsingInnovation.State d ℝ → ℝ}
    {I : IsingInnovation.State d ℝ → ℝ}
    (hX : ∀ n, MemLp (X n) 2 (μ.prod (labelMeasure d)))
    (hI : MemLp I 2 (μ.prod (labelMeasure d)))
    (hXlim : ∀ n, Tendsto (fun k => ∫ q,
      (BrownianGrid.uniformSum
        (IsingInnovation.innovation beta (fun t r => WienerSampler.sample r t) u)
        (IsingInnovation.finiteCovariance beta (fun t r => WienerSampler.sample r t)
          (ConnectedHull.root d) u n) T k q - X n q) ^ 2
        ∂μ.prod (labelMeasure d)) atTop (𝓝 0))
    (hXI : Tendsto (fun n => ∫ q, (X n q - I q) ^ 2
      ∂μ.prod (labelMeasure d)) atTop (𝓝 0))
    {J : Paths d → ℝ} (hJ : MemLp J 2 (observationLaw μ))
    (hJlim : Tendsto (fun k => ∫ x,
      (BrownianGrid.uniformSum (fun t x => innovationMap beta x u t)
        (continuousRootCovariance hb u) T k x - J x) ^ 2
        ∂observationLaw μ) atTop (𝓝 0)) :
    I =ᵐ[μ.prod (labelMeasure d)] J ∘ uniformObservation := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let B : ℝ≥0 → ℝ → ℝ := fun t r => WienerSampler.sample r t
  have hmB (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample
  have hcB (r : ℝ) : Continuous (fun t => B t r) :=
    (WienerSampler.sample r).continuous
  have hB : IsPreBrownianReal B uniform01 :=
    WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
  have hφ : MeasurePreserving (uniformObservation (d := d))
      (μ.prod (labelMeasure d)) (observationLaw μ) :=
    ⟨measurable_uniformObservation, rfl⟩
  let H : ℝ≥0 → IsingInnovation.State d ℝ → ℝ :=
    fun t q => continuousRootCovariance hb u t (uniformObservation q)
  have hH := continuousRootCovariance_uniformObservation_stronglyAdapted hmB hb u
  have hcH := continuousRootCovariance_uniformObservation_continuous_ae hd hμ hb hcrit u
  have hbH : ∀ᵐ q ∂μ.prod (labelMeasure d), ∀ t, |H t q| ≤ (1 : ℝ) :=
    Eventually.of_forall fun q t =>
      continuousRootCovariance_uniformObservation_abs_le_one hb u t q
  have hver := continuousRootCovariance_uniformObservation_eq_covariance_ae hd hμ hb hcrit u
  have hC2 (t : ℝ≥0) : MemLp (continuousRootCovariance hb u t) 2
      (observationLaw μ) := by
    apply MemLp.of_bound
      (((continuousRootCovariance_progressive hb u).stronglyAdapted t).mono
        ((filtration d).le t)).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using continuousRootCovariance_abs_le_one hb u t x
  have hi (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past
      (B := fun v t x => innovationMap beta x v t) (F := filtration d)
      (s := s) (t := t)
      (innovationMap_increment_indep_filtration hμ s t hst) u
  have hS (k : ℕ) := BrownianFiltrationGrid.uniformSum_memLp
    (innovationMap_isBrownianReal hμ u).toIsPreBrownianReal
    (innovationMap_stronglyAdapted beta u) hi
    (continuousRootCovariance hb u)
    (continuousRootCovariance_progressive hb u).stronglyAdapted hC2 T k
  have hJpull := BrownianGrid.meanSquare_limit_comp hφ
    (fun k => (hS k).aestronglyMeasurable) hJ.aestronglyMeasurable hJlim
  have hcoeff := IsingInnovation.finiteCovariance_tendsto_version_timeMeanSquare
    hμ uniform01 hB hmB hcB (ConnectedHull.root d) u T hver
  apply BrownianGrid.ae_eq_of_mean_square_limits hX hI
    (hJ.comp_measurePreserving hφ) hXI
  exact BrownianFiltrationGrid.tendsto_meanSquare_of_coefficient_interval
    (IsingInnovation.isBrownianReal_innovation hμ uniform01 hB hmB hcB u).toIsPreBrownianReal
    (IsingInnovation.innovation_martingale hμ uniform01 hB hmB hcB u).stronglyAdapted
    (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
      (IsingInnovation.innovation_increment_indep_filtration hμ uniform01 hB hmB hcB s t hst) u)
    (fun n => IsingInnovation.finiteCovariance beta B (ConnectedHull.root d) u n) H
    (fun n => IsingInnovation.finiteCovariance_stronglyAdapted beta B hmB
      (ConnectedHull.root d) u n) hH
    (fun n => Eventually.of_forall
      (IsingInnovation.finiteCovariance_continuous beta B hcB (ConnectedHull.root d) u n)) hcH
    (fun _ => 2) 1 (fun _ => by norm_num) (by norm_num)
    (fun n => Eventually.of_forall fun q t =>
      IsingInnovation.finiteCovariance_abs_le_two beta B (ConnectedHull.root d) u n t q) hbH
    T hX (hJ.comp_measurePreserving hφ) hXlim hJpull hcoeff

end Problem367.IsingObservationFactor

end

end OAI
