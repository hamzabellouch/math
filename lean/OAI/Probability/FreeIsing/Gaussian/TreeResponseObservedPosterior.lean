import OAI.Probability.FreeIsing.Gaussian.TreeResponsePlanted
import OAI.Probability.FreeIsing.Gaussian.TreeResponsePosterior
import OAI.Probability.FreeIsing.Posterior.NormalizedPosteriorLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance

theorem HasFreeIsingLaw.finiteObservation_posteriorResponse_eq_observedRow
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (u v : D) :
    posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun p => spinSign (p.1 u.1)) (fun p => spinSign (p.1 v.1)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      observedRow beta D u.1 t v.1 := by
  unfold posteriorResponse posteriorCovariance observedRow
  simp only [ite_eq_left v.property]
  exact hμ.finiteObservation_normalizedResponse D hD t u v

theorem HasFreeIsingLaw.finiteObservation_posteriorResponse_sq_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    {t : ℝ≥0} (ht : 0 < t) (u v : D) (hu : u.1.1 = []) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    Integrable (fun p => (posteriorResponse P (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2) P ∧
    (∫ p, (posteriorResponse P (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2 ∂P) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.1.length := by
  dsimp only
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have he := hμ.finiteObservation_posteriorResponse_eq_observedRow D hD t u v
  have he2 : (fun p => (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => observedRow beta D u.1 t v.1 p ^ 2 := by
    filter_upwards [he] with p hp
    exact congrArg (fun x : ℝ => x ^ 2) hp
  refine ⟨(integrable_observedRow_sq μ hbeta t hD u.property hu v.1).congr he2.symm, ?_⟩
  rw [integral_congr_ae he2]
  exact integral_observedRow_sq_le μ hbeta ht hD u.property hu v.1

theorem HasFreeIsingLaw.gaussian_posteriorResponse_sq_decay_of_exhaustion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ w, ∃ n, w ∈ D n)
    {t : ℝ≥0} (ht : 0 < t) (r v : TreeVertex d) (hr : r.1 = []) :
    Integrable (fun p => gaussianPosteriorResponse μ t r v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  apply hμ.gaussian_posteriorResponse_integrable_sq hbeta D hD hex t r v
    (pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le) _)
  obtain ⟨nr, hnr⟩ := hex r
  obtain ⟨nv, hnv⟩ := hex v
  filter_upwards [eventually_ge_atTop (max nr nv)] with n hn
  have hrn : r ∈ D n := hD (le_trans (le_max_left nr nv) hn) hnr
  have hvn : v ∈ D n := hD (le_trans (le_max_right nr nv) hn) hnv
  exact hμ.finiteObservation_posteriorResponse_sq_bound hbeta (D n) (hconn n) ht
    ⟨r, hrn⟩ ⟨v, hvn⟩ hr

theorem HasFreeIsingLaw.gaussian_posteriorResponse_sq_decay
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t) (r v : TreeVertex d) (hr : r.1 = []) :
    Integrable (fun p => gaussianPosteriorResponse μ t r v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  obtain ⟨D, hD, hc, hex⟩ := exists_connected_exhaustion r
  exact hμ.gaussian_posteriorResponse_sq_decay_of_exhaustion hbeta D hD
    (fun n => (hc n).1) hex ht r v hr

theorem HasFreeIsingLaw.gaussian_posteriorResponse_row_energy
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (r : TreeVertex d) (hr : r.1 = []) :
    (∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Summable (fun v => gaussianPosteriorResponse μ t r v p ^ 2)) ∧
    Integrable (fun p => ∑' v, gaussianPosteriorResponse μ t r v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, ∑' v, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  have hb (v : TreeVertex d) := hμ.gaussian_posteriorResponse_sq_decay hbeta ht r v hr
  have hnonneg := mul_nonneg (sq_nonneg (Real.tanh beta)) (gaussianContraction_pos beta t).le
  have hsmall := gaussian_radial_ratio_lt_one ht hcrit
  have hs : Summable (fun v => ∫ p, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    summable_of_tree_radial_le (C := 1)
      (fun v => integral_nonneg (fun p => sq_nonneg _))
      (fun v => by simpa only [one_mul] using (hb v).2) hnonneg hsmall
  obtain ⟨hae, hint⟩ := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun v => (hb v).1) hs
  refine ⟨hae, hint, ?_⟩
  simpa only [one_mul] using integral_tsum_sq_le_of_tree_radial_bound (C := 1)
    (fun v => (hb v).1) (fun v => by simpa only [one_mul] using (hb v).2) hnonneg hsmall

theorem HasFreeIsingLaw.gaussian_posteriorResponse_row_energy_tail
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (r : TreeVertex d) (hr : r.1 = []) (L : ℕ) :
    (∫ p, ∑' v : TreeVertex d, if L < v.1.length then
        gaussianPosteriorResponse μ t r v p ^ 2 else 0
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) *
        (((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  have hb (v : TreeVertex d) := hμ.gaussian_posteriorResponse_sq_decay hbeta ht r v hr
  simpa only [one_mul] using integral_tsum_sq_cutoff_le_of_tree_radial_bound (C := 1)
    (fun v => (hb v).1) (fun v => by simpa only [one_mul] using (hb v).2)
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le)
    (gaussian_radial_ratio_lt_one ht hcrit) L

end Problem367

end

end OAI
