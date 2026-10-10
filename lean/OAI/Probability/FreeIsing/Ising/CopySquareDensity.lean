import OAI.Probability.FreeIsing.Ising.CanonicalArtanh
import OAI.Probability.FreeIsing.Ising.ContinuousCopyDensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySquareDensity
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy
open IsingContinuousCopyDensity StoppedTimePrimitive

variable {d : ℕ} {beta : ℝ}

def noise (hb : 0 ≤ beta) (t : ℝ≥0) (q : Joint d) : ℝ :=
  ∑' v, (response hb v true t q - response hb v false t q) ^ 2

def drift (beta : ℝ) (t : ℝ≥0) (q : Joint d) : ℝ :=
  canonicalResponseDrift beta (ConnectedHull.root d) t (projection true q) -
    canonicalResponseDrift beta (ConnectedHull.root d) t (projection false q)

theorem continuousDrift_eq_raw_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (t : ℝ≥0) :
    (fun q => copyContinuousPosterior beta (ConnectedHull.root d) j t q *
      ∑' v, response hb v j t q ^ 2) =ᵐ[copies beta μ]
      fun q => canonicalResponseDrift beta (ConnectedHull.root d) t (projection j q) := by
  filter_upwards [ae_all_iff.mpr (fun v => response_eq_raw_ae hd hμ hb hcrit v j t),
    (copyContinuousPosterior_modification hd hμ hb hcrit (ConnectedHull.root d) j).2 t]
    with q hrow hp
  unfold canonicalResponseDrift
  rw [hp]
  congr 1
  unfold infiniteGibbsResponseRow
  apply tsum_congr
  intro v
  apply congrArg (fun r : ℝ => r ^ 2)
  simpa only [responseRow, Real.toNNReal_coe] using hrow v

theorem density_eq_noise_add_drift_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (t : ℝ≥0) :
    continuousDensity hb t =ᵐ[copies beta μ]
      fun q => noise hb t q + 2 * continuousDifference beta (ConnectedHull.root d) t q *
        drift beta t q := by
  filter_upwards [continuousDrift_eq_raw_ae hd hμ hb hcrit true t,
    continuousDrift_eq_raw_ae hd hμ hb hcrit false t] with q hl hr
  unfold continuousDensity DiscrepancyEnergy.density noise drift
  rw [hl, hr]

theorem stopped_noise_add_drift_eq_density_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) (t : ℝ≥0) :
    (fun q => stopDensity (noise hb) τ t q +
      2 * stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ t q *
        stopDensity (drift beta) τ t q) =ᵐ[copies beta μ]
      stopDensity (continuousDensity hb) τ t := by
  filter_upwards [density_eq_noise_add_drift_ae hd hμ hb hcrit t] with q hq
  by_cases ht : (t : WithTop ℝ≥0) ≤ τ q
  · simp only [stopDensity, ht, ite_true, stoppedProcess_eq_of_le ht]
    exact hq.symm
  · simp only [stopDensity, ht, ite_false, mul_zero, add_zero]

theorem integral_stopped_noise_add_drift_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) (s : ℝ) :
    (∫ q, stopDensity (noise hb) τ s.toNNReal q +
      2 * stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ s.toNNReal q *
        stopDensity (drift beta) τ s.toNNReal q ∂copies beta μ) =
      ∫ q, if (s.toNNReal : WithTop ℝ≥0) ≤ τ q then
        IsingCopyEnergy.density beta (ConnectedHull.root d) s q else 0
        ∂copies beta μ := by
  exact (integral_congr_ae
    (stopped_noise_add_drift_eq_density_ae hd hμ hb hcrit τ s.toNNReal)).trans
      (integral_stopDensity_eq_actual hd hμ hb hcrit τ s)

theorem integral_integral_stopped_noise_add_drift_eq_actual
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (τ : Joint d → WithTop ℝ≥0) (T : ℝ≥0) :
    (∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
      stopDensity (noise hb) τ s.toNNReal q +
        2 * stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ s.toNNReal q *
          stopDensity (drift beta) τ s.toNNReal q ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ q,
        if (s.toNNReal : WithTop ℝ≥0) ≤ τ q then
          IsingCopyEnergy.density beta (ConnectedHull.root d) s q else 0
          ∂copies beta μ := by
  apply intervalIntegral.integral_congr
  intro s _
  exact integral_stopped_noise_add_drift_eq_actual hd hμ hb hcrit τ s

end Problem367.IsingCopySquareDensity

end

end OAI
