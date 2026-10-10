import OAI.Probability.FreeIsing.Brownian.MeanSquareDescent
import OAI.Probability.FreeIsing.Ising.CanonicalCoordinateIdentification
import OAI.Probability.FreeIsing.Ising.CanonicalCovarianceIntegrals
import OAI.Probability.FreeIsing.Ising.ObservationPosteriorMartingale
import OAI.Probability.FreeIsing.Ising.PosteriorIntegralRepresentation
import OAI.Probability.FreeIsing.Martingales.IntegerIdentification

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem canonical_root_covariance_integrals_hasSum
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (T : ℝ≥0) (J : TreeVertex d → Paths d → ℝ)
    (hJ : ∀ w, MemLp (J w) 2 (observationLaw μ))
    (hJlim : ∀ w, Tendsto (fun n => ∫ x,
      (BrownianGrid.uniformSum (fun s x => innovationMap beta x w s)
        (continuousRootCovariance hb w) T n x - J w x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0)) :
    HasSum (fun w => (hJ w).toLp (J w))
      ((posterior_memLp beta μ (ConnectedHull.root d) T 2).toLp
        (posterior beta (ConnectedHull.root d) T)) := by
  let B : ℝ≥0 → ℝ → ℝ := fun s r => WienerSampler.sample r s
  have hmB (s : ℝ≥0) : Measurable (B s) :=
    (continuous_eval_const s).measurable.comp WienerSampler.measurable_sample
  have hcB (r : ℝ) : Continuous (fun s => B s r) :=
    (WienerSampler.sample r).continuous
  obtain ⟨X, I, hI, hM, hX, hXlim, hXI, _hmI, _htI, _hzero, hsum, _herror⟩ :=
    IsingInnovation.exists_posterior_integral_representation hμ hd hb hcrit
      uniform01 WienerSampler.sample_isBrownianReal.toIsPreBrownianReal
      hmB hcB (ConnectedHull.root d) T
  have hIJ (w : TreeVertex d) : I w =ᵐ[μ.prod (labelMeasure d)]
      J w ∘ uniformObservation := by
    exact canonical_covariance_coordinate_integral_eq_pullback hd hμ hb hcrit w T
      (fun n => hX n w) (hI w) (fun n => hXlim n w) (hXI w) (hJ w) (hJlim w)
  exact PredictableL2.hasSum_toLp_descend_of_comp_ae
    (measurePreserving_uniformObservation μ) J hJ
    (posterior_memLp beta μ (ConnectedHull.root d) T 2)
    I hI hM hIJ (Eventually.of_forall (fun _ => rfl)) hsum

theorem canonical_root_covariance_integrals_hasSum_all_time
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (J : TreeVertex d → ℝ≥0 → Paths d → ℝ)
    (hJM : ∀ w, Martingale (J w) (filtration d) (observationLaw μ))
    (hJ2 : ∀ w t, MemLp (J w t) 2 (observationLaw μ))
    (hJlim : ∀ w (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (BrownianIntegralProcess.stoppedUniformSum
          (fun s x => innovationMap beta x w s)
          (continuousRootCovariance hb w) N n t x - J w t x) ^ 2
          ∂observationLaw μ) atTop (𝓝 0)) (t : ℝ≥0) :
    HasSum (fun w => (hJ2 w t).toLp (J w t))
      ((posterior_memLp beta μ (ConnectedHull.root d) t 2).toLp
        (posterior beta (ConnectedHull.root d) t)) := by
  apply MartingaleIntegerIdentification.hasSum_of_positive_integer hJM
    (posterior_martingale hμ (ConnectedHull.root d)) hJ2
    (fun s => posterior_memLp beta μ (ConnectedHull.root d) s 2) ?_ t
  intro N hN
  have happrox (w : TreeVertex d) : Tendsto (fun n => ∫ x,
      (BrownianGrid.uniformSum (fun s x => innovationMap beta x w s)
        (continuousRootCovariance hb w) N n x - J w N x) ^ 2 ∂observationLaw μ)
      atTop (𝓝 0) := by
    simpa only [BrownianIntegralProcess.stoppedUniformSum_terminal] using
      hJlim w N hN N le_rfl
  have hterminal := canonical_root_covariance_integrals_hasSum hd hμ hb hcrit
    (N : ℝ≥0) (fun w => J w N) (fun w => hJ2 w N) happrox
  exact PredictableL2.tendsto_integral_sq_error_of_hasSum
    (fun w => J w N) (fun w => hJ2 w N)
    (posterior_memLp beta μ (ConnectedHull.root d) N 2) hterminal

theorem exists_canonical_root_covariance_integral_representation
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∃ (J : TreeVertex d → ℝ≥0 → Paths d → ℝ)
      (hJ2 : ∀ w t, MemLp (J w t) 2 (observationLaw μ)),
      (∀ w, IsStronglyPredictable (filtration d) (J w)) ∧
      (∀ w, Martingale (J w) (filtration d) (observationLaw μ)) ∧
      (∀ w, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J w t x)) ∧
      (∀ w, J w 0 =ᵐ[observationLaw μ] 0) ∧
      (∀ w t, (∫ x, J w t x ∂observationLaw μ) = 0) ∧
      (∀ w t, (∫ x, J w t x ^ 2 ∂observationLaw μ) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
          continuousRootCovariance hb w s.toNNReal x ^ 2 ∂observationLaw μ) ∧
      (∀ w (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ x,
          (BrownianIntegralProcess.stoppedUniformSum
            (fun s x => innovationMap beta x w s)
            (continuousRootCovariance hb w) N n t x - J w t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0)) ∧
      (∀ t, HasSum (fun w => (hJ2 w t).toLp (J w t))
        ((posterior_memLp beta μ (ConnectedHull.root d) t 2).toLp
          (posterior beta (ConnectedHull.root d) t))) := by
  obtain ⟨J, hJp, hJM, hJc, hJ2, hJ0, hJmean, hJenergy, hJlim⟩ :=
    exists_canonical_root_covariance_integrals hd hμ hb hcrit
  exact ⟨J, hJ2, hJp, hJM, hJc, hJ0, hJmean, hJenergy, hJlim,
    canonical_root_covariance_integrals_hasSum_all_time hd hμ hb hcrit J hJM hJ2 hJlim⟩

end Problem367.IsingObservationFactor

end

end OAI
