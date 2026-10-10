import OAI.Probability.FreeIsing.Ising.CanonicalNormalizedField
import OAI.Probability.FreeIsing.Ising.CanonicalResponseIntegrals
import OAI.Probability.FreeIsing.Ising.CopiedDriftDecomposition
import OAI.Probability.FreeIsing.Ising.CopyResponseIdentification
import OAI.Probability.FreeIsing.Ising.CopySquareDensity
import OAI.Probability.FreeIsing.Ising.JoinedResponseIntegrals
import OAI.Probability.FreeIsing.Ising.StoppedSquareAssembly

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem variance_analysis_of_joined_decomposition
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (S : IsingJoinedResponseIntegrals.IntegralSystem hb μ)
    (hrep : ∀ᵐ z ∂copies beta μ, ∀ t,
      continuousDifference beta (ConnectedHull.root d) t z =
        (S.total true t z - S.total false t z) +
          nnrealTimePrimitive (copyResponseDriftDifference beta (ConnectedHull.root d)) t z)
    (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ z,
      (field beta (ConnectedHull.root d) t.toNNReal z.2.1 -
        field beta (ConnectedHull.root d) t.toNNReal z.2.2) ^ 2 ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ z,
        (field beta (ConnectedHull.root d) s.toNNReal z.2.1 -
          field beta (ConnectedHull.root d) s.toNNReal z.2.2) ^ 2 ∂copies beta μ) t =
        ∫ z, density beta (ConnectedHull.root d) t z ∂copies beta μ) := by
  have hM := (S.total_martingale true).sub (S.total_martingale false)
  have h2 (t : ℝ≥0) := (S.total_memLp true t).sub (S.total_memLp false t)
  have hc : ∀ᵐ z ∂copies beta μ, Continuous (fun t => S.total true t z - S.total false t z) := by
    filter_upwards [S.total_continuous true, S.total_continuous false] with z hl hr
    exact hl.sub hr
  have hp := (S.total_predictable true).isStronglyProgressive.sub
    (S.total_predictable false).isStronglyProgressive
  have hQ : Martingale (fun t z => (S.total true t z - S.total false t z) ^ 2 -
      nnrealTimePrimitive (copyResponseNoiseEnergy hb) t z)
      ContinuousCopyBrownian.joinedFiltration (copies beta μ) :=
    S.difference_compensatedSquare
  apply actual_variance_analysis_of_common_local_square hd hμ hb hcrit (ConnectedHull.root d) T
  intro n t ht
  have hs := stopped_difference_energy_of_representation hd hμ hb hcrit hM h2 hc hp hQ hrep n
    ((isLocalizingSequence_commonPosteriorExit hd hμ hb hcrit (ConnectedHull.root d)).isStoppingTime n)
    (fun _ => le_rfl) t
  apply hs.trans
  have hnoise : IsingCopySquareDensity.noise (d := d) hb = copyResponseNoiseEnergy hb := by
    funext s z
    rfl
  have hdrift : IsingCopySquareDensity.drift (d := d) beta =
      copyResponseDriftDifference beta (ConnectedHull.root d) := by
    funext s z
    rfl
  simpa only [hnoise, hdrift, mul_assoc] using
    IsingCopySquareDensity.integral_integral_stopped_noise_add_drift_eq_actual
      hd hμ hb hcrit (commonPosteriorExit beta (ConnectedHull.root d) n) t

theorem actual_variance_analysis
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ z,
      (field beta (ConnectedHull.root d) t.toNNReal z.2.1 -
        field beta (ConnectedHull.root d) t.toNNReal z.2.2) ^ 2 ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ z,
        (field beta (ConnectedHull.root d) s.toNNReal z.2.1 -
          field beta (ConnectedHull.root d) s.toNNReal z.2.2) ^ 2 ∂copies beta μ) t =
        ∫ z, density beta (ConnectedHull.root d) t z ∂copies beta μ) := by
  obtain ⟨I, Y, hI2, hY2, hI, hIlim, _hYp, hYM, hYc, _hY0,
      _hYiso, hYsum, _hYmax, _hQ, _hAint, _hAc⟩ :=
    exists_canonical_root_response_integrals hd hμ hb hcrit
  obtain ⟨S⟩ := IsingJoinedResponseIntegrals.exists_integrals hd hμ hb hcrit
  have hfield := canonical_field_eq_normalized_integral hd hμ hb hcrit
    (fun a => (hI a).2.1) hYM hI2 hY2 (fun a => (hI a).2.2) hYc hYsum hIlim
  have hcopy := rootResponse_sum_eq_copy_all_times hμ hb
    hI2 hY2 S.channel_memLp S.total_memLp hYc S.total_continuous
    hIlim S.channel_limit hYsum S.total_sum
  have hrep := copied_difference_decomposition hμ hb (ConnectedHull.root d)
    hfield (fun j => hcopy.mono (fun z hz => hz j))
  exact variance_analysis_of_joined_decomposition hd hμ hb hcrit S hrep T

end Problem367.IsingObservationFactor

end

end OAI
