import OAI.Probability.FreeIsing.Gibbs.CovarianceNativeRowCauchy
import OAI.Probability.FreeIsing.Ising.CovarianceTotalEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem finiteCovariance_timeEnergy_eq
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (n : ℕ) (T : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    (∑' u, ∫ r in (0 : ℝ)..(T : ℝ),
      ∫ q, finiteCovariance beta B v u n r.toNNReal q ^ 2 ∂P) =
      ∫ q, finiteGibbsSpinMean beta v n
        (fun i => (T : ℝ) * spinSign (q.1 i) + B T (q.2 i)) ^ 2 ∂P := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let Q := (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P
  have heq (u : TreeVertex d) :
      (∫ p : ℝ × State d A, finiteGibbsCovariance beta v u n
        (brownianIsingObservationR (fun _ : TreeVertex d => B) p) ^ 2 ∂Q) =
      ∫ r in (0 : ℝ)..(T : ℝ),
        ∫ q, finiteCovariance beta B v u n r.toNNReal q ^ 2 ∂P := by
    have h := integral_brownianIsingObservationR_eq_interval P
      (fun _ : TreeVertex d => B) (fun z => finiteGibbsCovariance beta v u n z ^ 2)
      T.coe_nonneg (integrable_finiteGibbsCovariance_sq beta v u n
        (measurable_brownianIsingObservationR (fun _ => hmB) (fun _ => hcB)))
    simpa only [finiteCovariance, plantedArrayObservation,
      ArrayPosteriorStationarity.spinArray, add_comm] using h
  calc
    _ = ∑' u, ∫ p : ℝ × State d A, finiteGibbsCovariance beta v u n
        (brownianIsingObservationR (fun _ : TreeVertex d => B) p) ^ 2 ∂Q :=
      (tsum_congr heq).symm
    _ = _ := by
      have h := hμ.finiteGibbsCovariance_timeEnergy_eq (fun _ : TreeVertex d => ν)
        (fun _ => hB) (fun _ => hmB) (fun _ => hcB) v n T.coe_nonneg
      change (∑' u, ∫ p : ℝ × State d A, finiteGibbsCovariance beta v u n
        (brownianIsingObservationR (fun _ : TreeVertex d => B) p) ^ 2 ∂Q) = _ at h
      refine h.trans ?_
      apply integral_congr_ae
      filter_upwards with q
      congr 2
      funext i
      simp only [brownianIsingObservationR, Real.toNNReal_coe]

theorem finiteCovariance_timeEnergy_tendsto
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    Tendsto (fun n => ∑' u, ∫ r in (0 : ℝ)..(T : ℝ),
      ∫ q, finiteCovariance beta B v u n r.toNNReal q ^ 2 ∂P) atTop
      (𝓝 (∫ q, posterior beta B v T q ^ 2 ∂P)) := by
  have h := hμ.finiteGibbsSpinMean_brownian_tendsto_integral_sq
    (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) T v
  have ht := h.congr' (Eventually.of_forall fun n =>
    (finiteCovariance_timeEnergy_eq hμ ν hB hmB hcB v n T).symm)
  simpa only [posterior, plantedArrayObservation,
    ArrayPosteriorStationarity.spinArray, add_comm] using ht

end Problem367.IsingInnovation

end

end OAI
