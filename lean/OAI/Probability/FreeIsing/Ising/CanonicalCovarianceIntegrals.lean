import OAI.Probability.FreeIsing.Brownian.IntegralHorizon
import OAI.Probability.FreeIsing.Ising.ContinuousRootResponse
import OAI.Probability.FreeIsing.Ising.ObservationIndependence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)}

theorem exists_canonical_root_covariance_integrals
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∃ J : TreeVertex d → ℝ≥0 → Paths d → ℝ,
      (∀ w, IsStronglyPredictable (filtration d) (J w)) ∧
      (∀ w, Martingale (J w) (filtration d) (observationLaw μ)) ∧
      (∀ w, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J w t x)) ∧
      (∀ w t, MemLp (J w t) 2 (observationLaw μ)) ∧
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
            ∂observationLaw μ) atTop (𝓝 0)) := by
  have hex (w : TreeVertex d) :=
    BrownianIntegralProcess.exists_global_continuous_uniform_integral
      (innovationMap_isBrownianReal hμ w).toIsPreBrownianReal
      (innovationMap_stronglyAdapted beta w)
      (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
        (B := fun w s x => innovationMap beta x w s)
        (F := filtration d)
        (innovationMap_increment_indep_filtration hμ s t hst) w)
      (innovationMap_isBrownianReal hμ w).cont
      (continuousRootCovariance_progressive hb w).stronglyAdapted
      (continuousRootCovariance_continuous_ae hd hμ hb hcrit w)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (Eventually.of_forall (fun x t => continuousRootCovariance_abs_le_one hb w t x))
  choose J hJp hJM hJc hJ2 hJ0 hJmean hJenergy hJlim using hex
  exact ⟨J, hJp, hJM, hJc, hJ2, hJ0, hJmean, hJenergy, hJlim⟩

end Problem367.IsingObservationFactor

end

end OAI
