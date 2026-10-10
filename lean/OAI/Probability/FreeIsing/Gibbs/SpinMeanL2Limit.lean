import OAI.Probability.FreeIsing.Energy.FiniteIsingCrossEnergy
import OAI.Probability.FreeIsing.Gibbs.CovarianceCriticalEnergy
import OAI.Probability.FreeIsing.Stochastic.FiniteObservationFiltrationLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace Problem367

theorem HasFreeIsingLaw.finiteGibbsSpinMean_brownian_tendsto_meanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (v : TreeVertex d) (t : ℝ≥0) :
    Tendsto (fun n => ∫ p,
      (finiteGibbsSpinMean beta v n (brownianIsingObservationR B ((t : ℝ), p)) -
        infiniteGibbsSpinMean beta v (brownianIsingObservationR B ((t : ℝ), p))) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let E : Filtration ℕ (inferInstance : MeasurableSpace
      ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :=
    ⟨fun n => FiniteIsingFiltering.observationFiltration B hmB (connectedExhaustion v n) t,
      FiniteIsingFiltering.observationFiltration_time_monotone B hmB
        (connectedExhaustion_monotone v) t,
      fun n => (FiniteIsingFiltering.observationFiltration B hmB (connectedExhaustion v n)).le t⟩
  let sigma := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) => spinSign (p.1 v)
  have hfinite n : (fun p => finiteGibbsSpinMean beta v n
      (brownianIsingObservationR B ((t : ℝ), p))) =ᵐ[P] P[sigma | E n] := by
    exact FiniteIsingFiltering.mean_eq_condExp_history hμ ν hB hmB
      (connectedExhaustion v n) (connectedExhaustion_connected v n)
      ⟨v, mem_connectedExhaustion v n⟩ t
  have hsup : (⨆ n, E n) = MeasurableSpace.comap
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
      inferInstance := by
    change (⨆ n, FiniteIsingFiltering.observationFiltration B hmB (connectedExhaustion v n) t) = _
    rw [FiniteIsingFiltering.iSup_observationFiltration_eq_arrayObservationFiltration
      B hmB (connectedExhaustion v) (fun w => (eventually_mem_connectedExhaustion v w).exists) t,
      arrayObservationFiltration, arrayNaturalFiltration_eq_comap]
    congr 1
    funext p i s
    exact add_comm _ _
  have hinfinite : (fun p => infiniteGibbsSpinMean beta v
      (brownianIsingObservationR B ((t : ℝ), p))) =ᵐ[P] P[sigma | ⨆ n, E n] := by
    rw [hsup]
    filter_upwards [hμ.infiniteGibbsSpinMean_eq_brownian_past ν hB hmB t v] with p hp
    calc
      infiniteGibbsSpinMean beta v (brownianIsingObservationR B ((t : ℝ), p)) =
          infiniteGibbsSpinMean beta v
            (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) := by
        apply congrArg (infiniteGibbsSpinMean beta v)
        funext i
        simp only [brownianIsingObservationR, Real.toNNReal_coe]
      _ = _ := hp
  have hlim := tendsto_integral_sq_sub_condExp_of_bounded P E sigma 1
    (Eventually.of_forall fun p => by cases h : p.1 v <;> norm_num [sigma, spinSign, h])
  apply hlim.congr
  intro n
  apply integral_congr_ae
  filter_upwards [hfinite n, hinfinite] with p hn hi
  rw [hn, hi]

end Problem367

end

end OAI
