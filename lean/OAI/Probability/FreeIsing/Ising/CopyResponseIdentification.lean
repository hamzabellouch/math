import OAI.Probability.FreeIsing.Brownian.MeanSquarePullback
import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse
import OAI.Probability.FreeIsing.Ising.CopyIntegralLimits
import OAI.Probability.FreeIsing.Ising.ObservationIndependence
import OAI.Probability.FreeIsing.Stochastic.StoppedIntegralAssociativity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy BrownianIntegralProcess

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
  [IsProbabilityMeasure μ]

private theorem response_stoppedUniformSum_memLp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (a : TreeVertex d) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedUniformSum (fun s x => innovationMap beta x a s)
      (continuousRootResponse hb a) T n t) 2 (observationLaw μ) := by
  apply StoppedIntegralAssociativity.stoppedUniformSum_memLp
    (fun s => ((innovationMap_isBrownianReal hμ a).toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval s).memLp_two)
    (continuousRootResponse_progressive hb a).stronglyAdapted
  exact Eventually.of_forall (fun x s => continuousRootResponse_abs_le_one hb a s x)

private theorem response_stoppedUniformSum_copy_memLp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (j : Bool) (a : TreeVertex d) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    MemLp (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
      (fun s p => continuousRootResponse hb a s (projection j p)) T n t)
      2 (copies beta μ) := by
  have hp := copyProjection_measurePreserving beta μ j
  apply ((response_stoppedUniformSum_memLp hμ hb a T n t).comp_measurePreserving hp).ae_eq
  filter_upwards [stoppedUniformSum_copy_eq_ae (beta := beta) (μ := μ)
    j a (continuousRootResponse hb a)] with q hq
  exact (hq T n t).symm

theorem rootResponse_integral_eq_copy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (j : Bool) (a : TreeVertex d)
    {I : ℝ≥0 → Paths d → ℝ} {J : ℝ≥0 → Joint d → ℝ}
    (hI2 : ∀ t, MemLp (I t) 2 (observationLaw μ))
    (hJ2 : ∀ t, MemLp (J t) 2 (copies beta μ))
    (hIlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x a s)
          (continuousRootResponse hb a) N n t x - I t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0))
    (hJlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
          (fun s p => continuousRootResponse hb a s (projection j p)) N n t q -
            J t q) ^ 2 ∂copies beta μ) atTop (𝓝 0))
    (t : ℝ≥0) :
    (fun q => I t (projection j q)) =ᵐ[copies beta μ] J t := by
  obtain ⟨N, hN⟩ := exists_nat_ge t
  have ht : t ≤ ((N + 1 : ℕ) : ℝ≥0) :=
    hN.trans (by exact_mod_cast Nat.le_succ N)
  have hp := copyProjection_measurePreserving beta μ j
  exact BrownianGrid.ae_eq_of_mean_square_limits
    (fun n => response_stoppedUniformSum_copy_memLp hμ hb j a ((N + 1 : ℕ) : ℝ≥0) n t)
    ((hI2 t).comp_measurePreserving hp) (hJ2 t)
    (integer_stoppedUniformSum_limits_copy j a
      (continuousRootResponse_progressive hb a).stronglyAdapted
      hI2 hIlim (N + 1) (Nat.succ_pos N) t ht)
    (hJlim (N + 1) (Nat.succ_pos N) t ht)

theorem rootResponse_integral_eq_copy_all_times
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (j : Bool) (a : TreeVertex d)
    {I : ℝ≥0 → Paths d → ℝ} {J : ℝ≥0 → Joint d → ℝ}
    (hI2 : ∀ t, MemLp (I t) 2 (observationLaw μ))
    (hJ2 : ∀ t, MemLp (J t) 2 (copies beta μ))
    (hcI : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => I t x))
    (hcJ : ∀ᵐ q ∂copies beta μ, Continuous (fun t => J t q))
    (hIlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x a s)
          (continuousRootResponse hb a) N n t x - I t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0))
    (hJlim : ∀ N : ℕ, 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
          (fun s p => continuousRootResponse hb a s (projection j p)) N n t q -
            J t q) ^ 2 ∂copies beta μ) atTop (𝓝 0)) :
    ∀ᵐ q ∂copies beta μ, ∀ t, I t (projection j q) = J t q := by
  have hp := copyProjection_measurePreserving beta μ j
  have hcI' : ∀ᵐ q ∂copies beta μ,
      Continuous (fun t => I t (projection j q)) := by
    apply ae_of_ae_map (p := fun x => Continuous (fun t => I t x)) hp.aemeasurable
    simpa only [hp.map_eq] using hcI
  have he : (fun q t => I t (projection j q)) =ᵐ[copies beta μ]
      (fun q t => J t q) :=
    ae_eq_of_continuous_of_evaluation_ae_eq hcI' hcJ
      (rootResponse_integral_eq_copy hμ hb j a hI2 hJ2 hIlim hJlim)
  filter_upwards [he] with q hq
  exact congrFun hq

theorem rootResponse_sum_eq_copy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (j : Bool)
    {I : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Y : ℝ≥0 → Paths d → ℝ}
    {J : TreeVertex d → ℝ≥0 → Joint d → ℝ} {Z : ℝ≥0 → Joint d → ℝ}
    (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
    (hY2 : ∀ t, MemLp (Y t) 2 (observationLaw μ))
    (hJ2 : ∀ a t, MemLp (J a t) 2 (copies beta μ))
    (hZ2 : ∀ t, MemLp (Z t) 2 (copies beta μ))
    (hIlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x a s)
          (continuousRootResponse hb a) N n t x - I a t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0))
    (hJlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
          (fun s p => continuousRootResponse hb a s (projection j p)) N n t q -
            J a t q) ^ 2 ∂copies beta μ) atTop (𝓝 0))
    (hsumI : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t)))
    (hsumJ : ∀ t, HasSum (fun a => (hJ2 a t).toLp (J a t)) ((hZ2 t).toLp (Z t)))
    (t : ℝ≥0) :
    (fun q => Y t (projection j q)) =ᵐ[copies beta μ] Z t := by
  have hp := copyProjection_measurePreserving beta μ j
  have hs := PredictableL2.hasSum_toLp_comp_measurePreserving hp
    (fun a => I a t) (fun a => hI2 a t) (hY2 t) (hsumI t)
  have hs' : HasSum
      (fun a => ((hI2 a t).comp_measurePreserving hp).toLp (I a t ∘ projection j))
      ((hZ2 t).toLp (Z t)) := by
    apply (hsumJ t).congr_fun
    intro a
    exact MemLp.toLp_congr _ _
      (rootResponse_integral_eq_copy hμ hb j a (hI2 a) (hJ2 a)
        (hIlim a) (hJlim a) t)
  exact (MemLp.toLp_eq_toLp_iff ((hY2 t).comp_measurePreserving hp) (hZ2 t)).mp
    (hs.unique hs')

theorem rootResponse_sum_eq_copy_all_times
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {I : TreeVertex d → ℝ≥0 → Paths d → ℝ} {Y : ℝ≥0 → Paths d → ℝ}
    {J : Bool → TreeVertex d → ℝ≥0 → Joint d → ℝ}
    {Z : Bool → ℝ≥0 → Joint d → ℝ}
    (hI2 : ∀ a t, MemLp (I a t) 2 (observationLaw μ))
    (hY2 : ∀ t, MemLp (Y t) 2 (observationLaw μ))
    (hJ2 : ∀ j a t, MemLp (J j a t) 2 (copies beta μ))
    (hZ2 : ∀ j t, MemLp (Z j t) 2 (copies beta μ))
    (hcY : ∀ᵐ x ∂observationLaw μ, Continuous (fun t => Y t x))
    (hcZ : ∀ j, ∀ᵐ q ∂copies beta μ, Continuous (fun t => Z j t q))
    (hIlim : ∀ a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ x,
        (stoppedUniformSum (fun s x => innovationMap beta x a s)
          (continuousRootResponse hb a) N n t x - I a t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0))
    (hJlim : ∀ j a (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
      Tendsto (fun n => ∫ q,
        (stoppedUniformSum (fun s (p : Joint d) => p.1 a s)
          (fun s p => continuousRootResponse hb a s (projection j p)) N n t q -
            J j a t q) ^ 2 ∂copies beta μ) atTop (𝓝 0))
    (hsumI : ∀ t, HasSum (fun a => (hI2 a t).toLp (I a t)) ((hY2 t).toLp (Y t)))
    (hsumJ : ∀ j t,
      HasSum (fun a => (hJ2 j a t).toLp (J j a t)) ((hZ2 j t).toLp (Z j t))) :
    ∀ᵐ q ∂copies beta μ, ∀ j t, Y t (projection j q) = Z j t q := by
  have he (j : Bool) : (fun q t => Y t (projection j q)) =ᵐ[copies beta μ]
      (fun q t => Z j t q) := by
    have hp := copyProjection_measurePreserving beta μ j
    have hcY' : ∀ᵐ q ∂copies beta μ,
        Continuous (fun t => Y t (projection j q)) := by
      apply ae_of_ae_map (p := fun x => Continuous (fun t => Y t x)) hp.aemeasurable
      simpa only [hp.map_eq] using hcY
    exact ae_eq_of_continuous_of_evaluation_ae_eq hcY' (hcZ j)
      (rootResponse_sum_eq_copy hμ hb j hI2 hY2 (hJ2 j) (hZ2 j)
        hIlim (hJlim j) hsumI (hsumJ j))
  filter_upwards [ae_all_iff.mpr he] with q hq
  intro j t
  exact congrFun (hq j) t

end Problem367.IsingObservationFactor

end

end OAI
