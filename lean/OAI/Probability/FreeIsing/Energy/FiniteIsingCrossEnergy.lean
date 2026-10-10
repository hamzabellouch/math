import OAI.Probability.FreeIsing.Posterior.FiniteIsingFilteringRepresentation
import OAI.Probability.FreeIsing.Posterior.PlantedArrayCrossEnergy
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianHistory

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem mean_eq_condExp_history {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (t : ℝ≥0) :
    mean beta D v B t =ᵐ[μ.prod (Measure.infinitePi ν)]
      (μ.prod (Measure.infinitePi ν))[(fun p : State d Ω => spinSign (p.1 v)) |
        observationFiltration B hmB D t] := by
  rw [observationFiltration_eq_comap]
  exact (hμ.condExp_finiteIsingBrownian_past ν hB hmB D hD
    (fun eta => spinSign (eta v)) t).symm

theorem covariance_eq_condExp_history {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v u : D) (t : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi ν)
    let F := observationFiltration B hmB D
    covariance beta D v u B t =ᵐ[P] fun p =>
      P[(fun p : State d Ω => spinSign (p.1 v) * spinSign (p.1 u)) | F t] p -
      P[(fun p : State d Ω => spinSign (p.1 v)) | F t] p * mean beta D u B t p := by
  have hc := hμ.finiteIsingBrownianCovariance_eq_past ν hB hmB D hD v u t
  rw [← observationFiltration_eq_comap B hmB D t] at hc
  filter_upwards [hc, mean_eq_condExp_history hμ ν hB hmB D hD u t] with p hp hu
  dsimp only [posteriorCovariance] at hp
  exact hp.trans (by rw [hu])

theorem tendsto_cross_uniformSum {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v u : D) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ p, mean beta D v B T p *
      BrownianGrid.uniformSum
        (fun t p => plantedArrayObservation B signal u t p -
          nnrealTimePrimitive (mean beta D u B) t p)
        (covariance beta D v u B) T n p ∂μ.prod (Measure.infinitePi ν))
      atTop (𝓝 (∫ r in (0 : ℝ)..(T : ℝ),
        ∫ p, covariance beta D v u B r.toNNReal p ^ 2 ∂μ.prod (Measure.infinitePi ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (index : TreeVertex d) : IsProbabilityMeasure (ν index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  have hs (i : TreeVertex d) : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma i)) := (measurable_pi_apply i).comp measurable_signal
  have hbound (i : TreeVertex d) : ∀ p : State d Ω, |spinSign (p.1 i)| ≤ (1 : ℝ) := by
    intro p
    cases p.1 i <;> norm_num [spinSign]
  have hint : Integrable (fun p : State d Ω => spinSign (p.1 u))
      (μ.prod (Measure.infinitePi ν)) :=
    Integrable.of_bound ((hs u).comp measurable_fst).aestronglyMeasurable 1
      (Eventually.of_forall (hbound u))
  have hobs : StronglyAdapted (observationFiltration B hmB D)
      (fun t p => B u t (p.2 u) + (t : ℝ) * spinSign (p.1 u)) :=
    arrayNaturalFiltration_stronglyAdapted
      (fun i : D => plantedArrayObservation B signal i)
      (fun i t => plantedArrayObservation_measurable hmB measurable_signal i t) u
  have hl := FilteringCrossEnergy.tendsto_posterior_uniformSum_cross_energy
    (preBrownian_martingale_signalArrayFiltration μ ν hB hmB (u : TreeVertex d))
    (observationFiltration_le_signal B hmB D)
    (stronglyMeasurable_latent_signalArrayFiltration B hmB (hs v) 0)
    (Eventually.of_forall (hbound v)) hint (Eventually.of_forall (hbound u)) hobs
    (progressive_mean beta D u B hmB hcB)
    (mean_eq_condExp_history hμ ν hB hmB D hD u)
    (stronglyAdapted_covariance beta D v u B hmB)
    (Eventually.of_forall (continuous_covariance beta D v u B hcB))
    (show (0 : ℝ) ≤ 2 by norm_num)
    (Eventually.of_forall (fun p t => abs_covariance_le_two beta D v u B t p))
    (covariance_eq_condExp_history hμ ν hB hmB D hD v u) T
  apply hl.congr
  intro n
  apply integral_congr_ae
  filter_upwards [mean_eq_condExp_history hμ ν hB hmB D hD v T] with p hp
  exact congrArg (fun x : ℝ => x * BrownianGrid.uniformSum
    (fun t p => plantedArrayObservation B signal u t p -
      nnrealTimePrimitive (mean beta D u B) t p)
    (covariance beta D v u B) T n p) hp.symm

end Problem367.FiniteIsingFiltering

end

end OAI
