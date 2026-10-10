import OAI.Probability.FreeIsing.Ising.CopyGeodesicCorrelations
import OAI.Probability.FreeIsing.Trees.CoupledPathVariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem memLp_cavityObservable_difference
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v w : TreeVertex d) :
    MemLp (fun q => cavityObservable hbeta t v w q.2.1 -
      cavityObservable hbeta t v w q.2.2) 2 (copies beta μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  exact ((memLp_cavityObservable hμ hbeta t v w).comp_measurePreserving hl).sub
    ((memLp_cavityObservable hμ hbeta t v w).comp_measurePreserving hr)

theorem integral_cavityProduct_log_sq_le_twice_unweighted
    {ι : Type*} (s : Finset ι) (a b : ι → TreeVertex d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (t : ℝ≥0) :
    (∫ q, ((∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.1)) ^ 2 +
      (∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.2)) ^ 2) *
      (∑ i ∈ s, cavityLogDifference hbeta t (a i) (b i) q) ^ 2 ∂copies beta μ) ≤
      2 * ∫ q, (∑ i ∈ s, cavityLogDifference hbeta t (a i) (b i) q) ^ 2
        ∂copies beta μ := by
  have hθ : (Real.tanh beta) ^ 2 ≤ 1 := by
    have h0 := tanh_nonneg_of_beta_nonneg hbeta
    have h1 := Real.tanh_lt_one beta
    nlinarith
  exact integral_weighted_path_log_sq_le_twice_unweighted s hθ
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_fst.comp measurable_snd))
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_snd.comp measurable_snd))
    (fun i _ => (memLp_cavityObservable_difference hμ hbeta t (a i) (b i)).integrable_sq)

theorem integral_cavityProduct_sub_sq_le_twice_log_sum
    {ι : Type*} (s : Finset ι) (a b : ι → TreeVertex d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (t : ℝ≥0) :
    (∫ q, ((∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.1)) -
      (∏ i ∈ s, responseAttenuation (Real.tanh beta)
        (cavityObservable hbeta t (a i) (b i) q.2.2))) ^ 2 ∂copies beta μ) ≤
      2 * ∫ q, (∑ i ∈ s, cavityLogDifference hbeta t (a i) (b i) q) ^ 2
        ∂copies beta μ := by
  have hθ : (Real.tanh beta) ^ 2 ≤ 1 := by
    have h0 := tanh_nonneg_of_beta_nonneg hbeta
    have h1 := Real.tanh_lt_one beta
    nlinarith
  have h := integral_prod_responseAttenuation_sub_sq_le s hθ
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_fst.comp measurable_snd))
    (fun i _ => (measurable_cavityObservable hbeta t (a i) (b i)).comp
      (measurable_snd.comp measurable_snd))
    (fun i _ => (memLp_cavityObservable_difference hμ hbeta t (a i) (b i)).integrable_sq)
  exact h.2.2.trans (integral_cavityProduct_log_sq_le_twice_unweighted s a b hμ hbeta t)

end Problem367.IsingCopySpectral

end

end OAI
