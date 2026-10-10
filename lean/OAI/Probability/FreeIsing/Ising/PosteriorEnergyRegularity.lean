import OAI.Probability.FreeIsing.Gibbs.CovarianceCriticalEnergy
import OAI.Probability.FreeIsing.Ising.ObservationComparison

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace Problem367.IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

private theorem measurable_sample_time (t : ℝ≥0) :
    Measurable (fun u : ℝ => WienerSampler.sample u t) :=
  (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample

def posteriorEnergyDensity (beta : ℝ) (μ : Measure (TreeVertex d → IsingSpin))
    (v : TreeVertex d) (s : ℝ) : ℝ :=
  ∫ p, ∑' w : TreeVertex d,
    infiniteGibbsCovariance beta v w
      (brownianIsingObservationR
        (fun (_ : TreeVertex d) t u => WienerSampler.sample u t) (s, p)) ^ 2
    ∂μ.prod (labelMeasure d)

theorem integrableOn_posteriorEnergyDensity
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (v : TreeVertex d)
    {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (posteriorEnergyDensity beta μ v) (Ioc 0 T) := by
  have h := hμ.infiniteGibbsCovariance_timeEnergy
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ => measurable_sample_time)
    (fun _ u => (WienerSampler.sample u).continuous) v hT
  exact h.2.2.2.1.integral_prod_left

omit [IsProbabilityMeasure μ] in
private theorem posterior_secondMoment_eq_planted (v : TreeVertex d) (t : ℝ≥0) :
    (∫ x, posterior beta v t x ^ 2 ∂observationLaw μ) =
      ∫ p, infiniteGibbsSpinMean beta v
        (brownianIsingObservationR
          (fun (_ : TreeVertex d) u z => WienerSampler.sample z u) ((t : ℝ), p)) ^ 2
        ∂μ.prod (labelMeasure d) := by
  have hm : Measurable (fun x : Paths d => posterior beta v t x ^ 2) :=
    (((posterior_progressive beta v).stronglyAdapted t).mono
      ((filtration d).le t)).measurable.pow_const 2
  rw [observationLaw, integral_map measurable_uniformObservation.aemeasurable
    hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with p
  change infiniteGibbsSpinMean beta v
    (fun i => WienerSampler.sample (p.2 i) t + (t : ℝ) * spinSign (p.1 i)) ^ 2 = _
  exact congrArg (fun y : TreeVertex d → ℝ => infiniteGibbsSpinMean beta v y ^ 2)
    (funext fun i => by
      simp only [brownianIsingObservationR, Real.toNNReal_coe]
      exact add_comm _ _)

theorem posterior_secondMoment_eq_integral_energy
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    (∫ x, posterior beta v t x ^ 2 ∂observationLaw μ) =
      ∫ s in (0 : ℝ)..(t : ℝ), posteriorEnergyDensity beta μ v s := by
  let B := fun (_ : TreeVertex d) (t : ℝ≥0) (u : ℝ) => WienerSampler.sample u t
  have hmB : ∀ i t, Measurable (B i t) := fun _ => measurable_sample_time
  have hcB : ∀ i u, Continuous (fun t => B i t u) :=
    fun _ u => (WienerSampler.sample u).continuous
  have hB : ∀ i, IsPreBrownianReal (B i) uniform01 :=
    fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
  have he := (hμ.infiniteGibbsCovariance_timeEnergy_eq hd hbeta hcrit
    (fun _ => uniform01) hB hmB hcB v t.coe_nonneg).2
  have hi := (hμ.infiniteGibbsCovariance_timeEnergy
    (fun _ => uniform01) hB hmB hcB v t.coe_nonneg).2.2.2.1
  rw [integral_prod _ hi] at he
  rw [posterior_secondMoment_eq_planted, intervalIntegral.integral_of_le t.coe_nonneg]
  exact he.symm

theorem absolutelyContinuousOnInterval_posterior_secondMoment
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ => ∫ x, posterior beta v t.toNNReal x ^ 2 ∂observationLaw μ) 0 T := by
  have hi : IntervalIntegrable (posteriorEnergyDensity beta μ v) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (integrableOn_posteriorEnergyDensity hμ v hT)
  apply DiscrepancyEnergy.absolutelyContinuousOnInterval_congr_on
    (hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp))
  intro t ht
  rw [uIcc_of_le hT] at ht
  have he := posterior_secondMoment_eq_integral_energy hd hμ hbeta hcrit v t.toNNReal
  rw [Real.coe_toNNReal t ht.1] at he
  exact he.symm

theorem ae_deriv_posterior_secondMoment
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun u : ℝ => ∫ x, posterior beta v u.toNNReal x ^ 2 ∂observationLaw μ) t =
        posteriorEnergyDensity beta μ v t := by
  have hi : IntervalIntegrable (posteriorEnergyDensity beta μ v) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
      (integrableOn_posteriorEnergyDensity hμ v hT)
  apply DiscrepancyEnergy.ae_deriv_of_integral_representation (c := 0) hT hi
  intro t ht
  have he := posterior_secondMoment_eq_integral_energy hd hμ hbeta hcrit v t.toNNReal
  rw [Real.coe_toNNReal t ht.1] at he
  simpa only [zero_add] using he

end Problem367.IsingObservationInnovation

end

end OAI
