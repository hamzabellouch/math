import OAI.Probability.FreeIsing.Energy.NNRealBoundedDriftEnergy
import OAI.Probability.FreeIsing.Ising.CanonicalLocalSquare
import OAI.Probability.FreeIsing.Ising.CommonStopBounds
import OAI.Probability.FreeIsing.Ising.ContinuousCopyCoefficients
import OAI.Probability.FreeIsing.Ising.StoppedDifferenceBounds
import OAI.Probability.FreeIsing.Spectral.L2CompensatedDensityStopping

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy IsingContinuousCopyCoefficients

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def copyResponseNoiseEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (z : Joint d) : ℝ :=
  ∑' v : TreeVertex d, (response hb true v t z - response hb false v t z) ^ 2

lemma copyResponseNoiseEnergy_progressive (hb : 0 ≤ beta) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (copyResponseNoiseEnergy (d := d) hb) := by
  intro T
  let : MeasurableSpace (Joint d) := ContinuousCopyBrownian.joinedFiltration T
  exact StronglyMeasurable.tsum (fun v =>
    ((response_progressive hb true v T).sub (response_progressive hb false v T)).pow 2)

lemma copyResponseNoiseEnergy_nonneg (hb : 0 ≤ beta) (t : ℝ≥0) (z : Joint d) :
    0 ≤ copyResponseNoiseEnergy hb t z := tsum_nonneg (fun _ => sq_nonneg _)

lemma copyResponseNoiseEnergy_integrable (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Joint d => copyResponseNoiseEnergy hb p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod (copies beta μ)) := by
  obtain ⟨hl, hil⟩ := response_row_energy hd hμ hb hcrit true T
  obtain ⟨hr, hir⟩ := response_row_energy hd hμ hb hcrit false T
  exact DiscrepancyEnergy.integrable_sq_difference_row
    (fun v => (NNRealBoundedDriftEnergy.stronglyMeasurable_realExtension
      (response_progressive hb true v)).aestronglyMeasurable)
    (fun v => (NNRealBoundedDriftEnergy.stronglyMeasurable_realExtension
      (response_progressive hb false v)).aestronglyMeasurable)
    hil hir (hl.and hr)

theorem stopped_difference_energy_of_representation
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    {M : ℝ≥0 → Joint d → ℝ}
    (hM : Martingale M ContinuousCopyBrownian.joinedFiltration (copies beta μ))
    (h2 : ∀ t, MemLp (M t) 2 (copies beta μ))
    (hcM : ∀ᵐ z ∂copies beta μ, Continuous (fun t => M t z))
    (hpM : IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration M)
    (hQ : Martingale (fun t z => M t z ^ 2 -
      nnrealTimePrimitive (copyResponseNoiseEnergy hb) t z)
      ContinuousCopyBrownian.joinedFiltration (copies beta μ))
    (hrep : ∀ᵐ z ∂copies beta μ, ∀ t,
      continuousDifference beta (ConnectedHull.root d) t z = M t z +
        nnrealTimePrimitive (copyResponseDriftDifference beta (ConnectedHull.root d)) t z)
    (n : ℕ) {τ : Joint d → WithTop ℝ≥0}
    (hτ : IsStoppingTime ContinuousCopyBrownian.joinedFiltration.rightCont τ)
    (hle : ∀ z, τ z ≤ commonPosteriorExit beta (ConnectedHull.root d) n z)
    (T : ℝ≥0) :
    (∫ z, (stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ T z) ^ 2
      ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(T : ℝ), ∫ z,
        StoppedTimePrimitive.stopDensity (copyResponseNoiseEnergy hb) τ s.toNNReal z +
          2 * (stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ s.toNNReal z *
            StoppedTimePrimitive.stopDensity
              (copyResponseDriftDifference beta (ConnectedHull.root d)) τ s.toNNReal z)
        ∂copies beta μ := by
  let b := copyResponseDriftDifference beta (ConnectedHull.root d)
  let q := copyResponseNoiseEnergy (d := d) hb
  have hbi (N : ℕ) : Integrable (fun p : ℝ × Joint d => b p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod (copies beta μ)) := by
    simpa only [NNReal.coe_natCast] using
      copyResponseDriftDifference_integrable hμ hb (ConnectedHull.root d) (N : ℝ≥0)
  have hqi (N : ℕ) : Integrable (fun p : ℝ × Joint d => q p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) (N : ℝ))).prod (copies beta μ)) := by
    simpa only [NNReal.coe_natCast] using
      copyResponseNoiseEnergy_integrable hd hμ hb hcrit (N : ℝ≥0)
  have hpb := copyResponseDriftDifference_progressive beta (ConnectedHull.root d)
  have hpq := copyResponseNoiseEnergy_progressive (d := d) hb
  obtain ⟨hMs, hQs⟩ := L2CompensatedDensityStopping.stopped_martingale_and_compensated_density
    hM h2 hcM hpM hpq (Eventually.of_forall (fun z t => copyResponseNoiseEnergy_nonneg hb t z))
    hqi hQ hτ
  have hMps := (DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
    ContinuousCopyBrownian.joinedFiltration.le_rightCont hpM).stoppedProcess hτ
  have hbps := StoppedTimePrimitive.isStronglyProgressive_stopDensity
    (DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
      ContinuousCopyBrownian.joinedFiltration.le_rightCont hpb) hτ
  have hsrep : ∀ᵐ z ∂copies beta μ, ∀ t,
      stoppedProcess (continuousDifference beta (ConnectedHull.root d)) τ t z =
        stoppedProcess M τ t z + nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) t z := by
    filter_upwards [hrep] with z hz
    intro t
    rw [← StoppedTimePrimitive.stoppedProcess_primitive]
    exact hz _
  have hX : ∀ᵐ z ∂copies beta μ, ∀ t ≤ T,
      |stoppedProcess M τ t z + nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) t z| ≤
        2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
    filter_upwards [hsrep, ae_horizon_stopped_continuousDifference_bound
      hd hμ hb hcrit (ConnectedHull.root d) τ T] with z hz hbound
    intro t ht
    rw [← hz t]
    exact hbound t ht
  have hA : ∀ᵐ z ∂copies beta μ, ∀ t ≤ T,
      |nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) t z| ≤ (n : ℝ) + 1 :=
    (ae_all_abs_cutoffDriftPrimitive_le hμ hb (ConnectedHull.root d) n hle).mono
      (fun z hz t _ => hz t)
  obtain ⟨_, hsq⟩ := NNRealBoundedDriftEnergy.integral_sq_of_bounded_process_compensated
    hMs hQs hMps hbps
    (L2CompensatedDensityStopping.integrable_stopped_density_on_horizon hpb hbi hτ T)
    (L2CompensatedDensityStopping.integrable_stopped_density_on_horizon hpq hqi hτ T) hX hA
  have hzM : stoppedProcess M τ 0 =ᵐ[copies beta μ] 0 := by
    filter_upwards [hrep, continuousDifference_initial_zero hd hμ hb hcrit (ConnectedHull.root d)]
      with z hz hzero
    have hz0 := hz 0
    simp only [nnrealTimePrimitive, NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at hz0
    rw [stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ z from zero_le)]
    exact hz0.symm.trans hzero
  have hzint : (∫ z, stoppedProcess M τ 0 z ^ 2 ∂copies beta μ) = 0 := by
    calc
      _ = ∫ _z, (0 : ℝ) ∂copies beta μ := integral_congr_ae
        (hzM.mono (fun z hz => by simp only [hz, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0)]))
      _ = 0 := integral_zero _ _
  rw [hzint, zero_add] at hsq
  calc
    _ = ∫ z, (stoppedProcess M τ T z +
        nnrealTimePrimitive (StoppedTimePrimitive.stopDensity b τ) T z) ^ 2 ∂copies beta μ :=
      integral_congr_ae (hsrep.mono (fun z hz => congrArg (fun r : ℝ => r ^ 2) (hz T)))
    _ = _ := hsq.trans (by
      apply intervalIntegral.integral_congr
      intro s hs
      apply integral_congr_ae
      filter_upwards [hsrep] with z hz
      rw [← hz s.toNNReal])

end Problem367.IsingObservationFactor

end

end OAI
