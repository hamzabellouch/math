import OAI.Probability.FreeIsing.Conditioning.CopyCompensatedSquare
import OAI.Probability.FreeIsing.Ising.ContinuousCopyCoefficients

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingJoinedResponseIntegrals
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy
open IsingContinuousCopyCoefficients BrownianArrayFiltration

variable {d : ℕ} {beta : ℝ}

structure IntegralSystem (hb : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ] where
  channel : Bool → TreeVertex d → ℝ≥0 → Joint d → ℝ
  total : Bool → ℝ≥0 → Joint d → ℝ
  channel_memLp : ∀ j v t, MemLp (channel j v t) 2 (copies beta μ)
  total_memLp : ∀ j t, MemLp (total j t) 2 (copies beta μ)
  channel_predictable : ∀ j v, IsStronglyPredictable
    ContinuousCopyBrownian.joinedFiltration (channel j v)
  channel_martingale : ∀ j v, Martingale (channel j v)
    ContinuousCopyBrownian.joinedFiltration (copies beta μ)
  channel_continuous : ∀ j v, ∀ᵐ q ∂copies beta μ,
    Continuous (fun t => channel j v t q)
  channel_limit : ∀ j v (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
    Tendsto (fun n => ∫ q,
      (BrownianIntegralProcess.stoppedUniformSum
        (fun s (p : Joint d) => p.1 v s) (response hb j v) N n t q -
          channel j v t q) ^ 2 ∂copies beta μ) atTop (𝓝 0)
  total_predictable : ∀ j, IsStronglyPredictable
    ContinuousCopyBrownian.joinedFiltration (total j)
  total_martingale : ∀ j, Martingale (total j)
    ContinuousCopyBrownian.joinedFiltration (copies beta μ)
  total_continuous : ∀ j, ∀ᵐ q ∂copies beta μ, Continuous (fun t => total j t q)
  total_zero : ∀ j, total j 0 =ᵐ[copies beta μ] 0
  total_sum : ∀ j t, HasSum (fun v => (channel_memLp j v t).toLp (channel j v t))
    ((total_memLp j t).toLp (total j t))
  difference_compensatedSquare : Martingale (fun t q =>
    (total true t q - total false t q) ^ 2 -
      nnrealTimePrimitive (spatialSquareDensity
        (fun v s p => response hb true v s p - response hb false v s p)) t q)
    ContinuousCopyBrownian.joinedFiltration (copies beta μ)

theorem exists_integrals
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    Nonempty (IntegralSystem hb μ) := by
  have hB (v : TreeVertex d) := (IsingCopyBrownian.commonNoise_isBrownianReal hμ v).toIsPreBrownianReal
  have hBc (v : TreeVertex d) : ∀ᵐ q ∂copies beta μ,
      Continuous (fun t => q.1 v t) :=
    (IsingCopyBrownian.commonNoise_isBrownianReal hμ v).cont
  have hpast (s t : ℝ≥0) (hst : s ≤ t) :=
    IsingCopyBrownian.increment_indep_joinedFiltration hμ hst
  have hind (s t : ℝ≥0) (_hst : s ≤ t) : Pairwise fun v w =>
      IndepFun (fun q : Joint d => q.1 v t - q.1 v s)
        (fun q : Joint d => q.1 w t - q.1 w s) (copies beta μ) :=
    fun _ _ hvw => IsingCopyBrownian.commonNoise_increments_indep hμ s t hvw
  have hex (j : Bool) := exists_global_continuous_spatial_integral_compensatedSquare
    hB IsingCopyBrownian.commonNoise_stronglyAdapted hpast hind hBc
    (fun v => (response_progressive hb j v).stronglyAdapted)
    (response_continuous_ae hd hμ hb hcrit j)
    (C := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (fun v => Eventually.of_forall (fun q t => response_abs_le_one hb j v t q))
    (fun N => by simpa only [NNReal.coe_natCast] using
      response_energy_summable hd hμ hb hcrit j (N : ℝ≥0))
  choose I Y hI2 hY2 hI hlim hYp hYM hYc hY0 hYiso hYsum hYmax hYQ hYA hYseries using hex
  have hdiff := difference_compensatedSquare_of_spatial_integral_limits
    hB IsingCopyBrownian.commonNoise_stronglyAdapted hpast hind hBc
    (response_progressive hb true) (response_progressive hb false)
    (response_continuous_ae hd hμ hb hcrit true)
    (response_continuous_ae hd hμ hb hcrit false)
    (C := fun _ => (1 : ℝ)) (D := fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun v => Eventually.of_forall (fun q t => response_abs_le_one hb true v t q))
    (fun v => Eventually.of_forall (fun q t => response_abs_le_one hb false v t q))
    (fun N => by simpa only [NNReal.coe_natCast] using
      response_energy_summable hd hμ hb hcrit true (N : ℝ≥0))
    (fun N => by simpa only [NNReal.coe_natCast] using
      response_energy_summable hd hμ hb hcrit false (N : ℝ≥0))
    (hI2 true) (hI2 false) (hYM true).stronglyAdapted (hYM false).stronglyAdapted
    (hY2 true) (hY2 false) (hlim true) (hlim false) (hYsum true) (hYsum false)
  exact ⟨{
    channel := I
    total := Y
    channel_memLp := hI2
    total_memLp := hY2
    channel_predictable := fun j v => (hI j v).1
    channel_martingale := fun j v => (hI j v).2.1
    channel_continuous := fun j v => (hI j v).2.2
    channel_limit := hlim
    total_predictable := hYp
    total_martingale := hYM
    total_continuous := hYc
    total_zero := hY0
    total_sum := hYsum
    difference_compensatedSquare := hdiff.2 }⟩

end Problem367.IsingJoinedResponseIntegrals

end

end OAI
