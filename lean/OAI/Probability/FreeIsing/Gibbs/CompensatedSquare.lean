import OAI.Probability.FreeIsing.Estimates.FiniteIsingCompensatedSquare
import OAI.Probability.FreeIsing.Gibbs.CovarianceCompensator
import OAI.Probability.FreeIsing.Gibbs.SpinMeanL2Limit
import OAI.Probability.FreeIsing.Stochastic.GrowingFiltrationMartingale

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367

theorem finiteGibbsCovarianceCompensator_eq_quadraticCompensator
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (v : TreeVertex d) (n : ℕ)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (t : ℝ≥0) :
    finiteGibbsCovarianceCompensator beta v n B t =
      FiniteIsingFiltering.quadraticCompensator beta (connectedExhaustion v n)
        ⟨v, mem_connectedExhaustion v n⟩ B t := by
  classical
  funext p
  rw [FiniteIsingFiltering.quadraticCompensator_eq_integral_energy _ _ _ _ hcB]
  unfold finiteGibbsCovarianceCompensator
  rw [intervalIntegral.integral_of_le t.coe_nonneg,
    intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp only
  rw [finiteGibbsCovarianceEnergy_eq_sum, ← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro u hu
  rw [finiteGibbsCovariance_eq_finiteIsingBrownianCovariance]
  simp only [FiniteIsingFiltering.covariance, Real.coe_toNNReal r hr.1.le]

theorem stronglyAdapted_infiniteGibbsSpinMean_brownian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (beta : ℝ) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    StronglyAdapted
      (arrayObservationFiltration B hmB FiniteIsingFiltering.signal
        FiniteIsingFiltering.measurable_signal)
      (fun t p => infiniteGibbsSpinMean beta v
        (brownianIsingObservationR B ((t : ℝ), p))) := by
  let F := arrayObservationFiltration B hmB FiniteIsingFiltering.signal
    FiniteIsingFiltering.measurable_signal
  let X := plantedArrayObservation B FiniteIsingFiltering.signal
  have hX (i : TreeVertex d) : IsStronglyProgressive F (X i) := by
    apply (arrayNaturalFiltration_stronglyAdapted X
      (plantedArrayObservation_measurable hmB FiniteIsingFiltering.measurable_signal) i).isStronglyProgressive_of_continuous
    intro p
    exact (hcB i (p.2 i)).add (continuous_subtype_val.mul continuous_const)
  have h := (isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX).stronglyAdapted
  convert h using 1
  funext t p
  congr 1
  funext i
  simp only [brownianIsingObservationR, X, plantedArrayObservation,
    FiniteIsingFiltering.signal, Real.toNNReal_coe, add_comm]

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_compensatedSquare_martingale
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (v : TreeVertex d) :
    Martingale (fun (t : ℝ≥0) p =>
      infiniteGibbsSpinMean beta v (brownianIsingObservationR B ((t : ℝ), p)) ^ 2 -
        gibbsCovarianceCompensator beta v B t p)
      (arrayObservationFiltration B hmB FiniteIsingFiltering.signal
        FiniteIsingFiltering.measurable_signal)
      (μ.prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let F := fun n => FiniteIsingFiltering.observationFiltration B hmB (connectedExhaustion v n)
  let G := arrayObservationFiltration B hmB FiniteIsingFiltering.signal
    FiniteIsingFiltering.measurable_signal
  let X := fun n => FiniteIsingFiltering.mean beta (connectedExhaustion v n)
    ⟨v, mem_connectedExhaustion v n⟩ B
  let Y := fun (t : ℝ≥0) p => infiniteGibbsSpinMean beta v
    (brownianIsingObservationR B ((t : ℝ), p))
  have hX (n : ℕ) (t : ℝ≥0) : MemLp (X n t) 2 P :=
    FiniteIsingFiltering.memLp_mean P beta (connectedExhaustion v n)
      ⟨v, mem_connectedExhaustion v n⟩ B hmB t 2
  have hY : StronglyAdapted G Y :=
    stronglyAdapted_infiniteGibbsSpinMean_brownian beta v B hmB hcB
  have hY2 (t : ℝ≥0) : MemLp (Y t) 2 P := by
    apply MemLp.of_bound (hY.stronglyMeasurable.aestronglyMeasurable) 1
    exact Eventually.of_forall fun p => infiniteGibbsSpinMean_abs_le_one beta v _
  apply GrowingFiltrationMartingale.compensatedSquare_of_growing_limits F G
    (FiniteIsingFiltering.observationFiltration_time_monotone B hmB
      (connectedExhaustion_monotone v))
    (FiniteIsingFiltering.iSup_observationFiltration_eq_arrayObservationFiltration
      B hmB (connectedExhaustion v) (fun w => (eventually_mem_connectedExhaustion v w).exists))
    hX
    (fun n t => integrable_finiteGibbsCovarianceCompensator beta v n μ ν hmB hcB t)
    ?_ hY hY2 (stronglyAdapted_gibbsCovarianceCompensator beta v B hmB hcB)
    (hμ.integrable_gibbsCovarianceCompensator ν hB hmB hcB v) ?_
    (hμ.finiteGibbsCovarianceCompensator_tendsto_L1 hd hb hcrit ν hB hmB hcB v)
  · intro n
    have h := FiniteIsingFiltering.mean_compensatedSquare_martingale
      hμ ν hB hmB hcB (connectedExhaustion v n) (connectedExhaustion_connected v n)
      ⟨v, mem_connectedExhaustion v n⟩
    simpa only [X, finiteGibbsCovarianceCompensator_eq_quadraticCompensator beta v n B hcB] using h
  · intro t
    apply CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
      (fun n => hX n t) (hY2 t)
    exact hμ.finiteGibbsSpinMean_brownian_tendsto_meanSquare ν hB hmB v t

end Problem367

end

end OAI
