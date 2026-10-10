import OAI.Probability.FreeIsing.Gaussian.TreeResponsePlanted
import OAI.Probability.FreeIsing.Gaussian.TreeResponsePosterior
import OAI.Probability.FreeIsing.Posterior.NormalizedPosteriorLimit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

open PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance

lemma GaussianTreeResponse.measurable_observedRow {d : ℕ}
    (beta : ℝ) (D : Finset (TreeVertex d)) (r : TreeVertex d)
    (t : ℝ) (v : TreeVertex d) : Measurable (observedRow beta D r t v) := by
  classical
  unfold observedRow
  by_cases hv : v ∈ D
  · simp only [ite_eq_left hv]
    exact (measurable_response beta D r v).comp (measurable_observation t)
  · simp only [ite_eq_right hv]
    exact measurable_const

theorem HasFreeIsingLaw.observedRow_eq_posteriorResponse
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (r v : TreeVertex d)
    (hr : r ∈ D) (hv : v ∈ D) (t : ℝ≥0) :
    observedRow beta D r t v =ᵐ[μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation D t) inferInstance)
        (fun p => spinSign (p.1 r)) (fun p => spinSign (p.1 v)) := by
  have h := hμ.finiteObservation_normalizedResponse D hD t ⟨r, hr⟩ ⟨v, hv⟩
  filter_upwards [h] with p hp
  simpa only [observedRow, ite_eq_left hv, posteriorResponse, posteriorCovariance] using hp.symm

theorem HasFreeIsingLaw.observedRow_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (r : TreeVertex d)
    (hr : ∀ n, r ∈ D n) (hex : ∀ v, ∃ n, v ∈ D n) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => observedRow beta (D n) r t v p) atTop
        (𝓝 (gaussianPosteriorResponse μ t r v p)) := by
  have heq (n : ℕ) : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      v ∈ D n → observedRow beta (D n) r t v p =
        posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
          (fun p => spinSign (p.1 r)) (fun p => spinSign (p.1 v)) p := by
    by_cases hv : v ∈ D n
    · exact (hμ.observedRow_eq_posteriorResponse (D n) (hconn n) r v (hr n) hv t).mono
        (fun p hp _ => hp)
    · exact Filter.Eventually.of_forall (fun _ hv' => (hv hv').elim)
  obtain ⟨N, hN⟩ := hex v
  have hmem : ∀ᶠ n in atTop, v ∈ D n :=
    eventually_atTop.2 ⟨N, fun n hn => hD hn hN⟩
  filter_upwards [ae_all_iff.mpr heq,
    hμ.gaussian_posteriorResponse_tendsto_ae hbeta D hD hex t r v] with p hp hlim
  exact hlim.congr' (hmem.mono (fun n hn => (hp n hn).symm))

theorem HasFreeIsingLaw.observedRow_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (r : TreeVertex d)
    (hr : ∀ n, r ∈ D n) (hex : ∀ v, ∃ n, v ∈ D n) (t : ℝ≥0) (v : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      (observedRow beta (D n) r t v p - gaussianPosteriorResponse μ t r v p) ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  apply (hμ.gaussian_posteriorResponse_meanSquare hbeta D hD hex t r v).congr'
  obtain ⟨N, hN⟩ := hex v
  filter_upwards [eventually_ge_atTop N] with n hn
  apply integral_congr_ae
  filter_upwards [hμ.observedRow_eq_posteriorResponse (D n) (hconn n) r v
    (hr n) (hD hn hN) t] with p hp
  rw [hp]

theorem HasFreeIsingLaw.observedRow_full_meanSquare
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (r : TreeVertex d)
    (hr : ∀ n, r ∈ D n) (hrnil : r.1 = [])
    (hex : ∀ v, ∃ n, v ∈ D n) {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    (∀ n, Summable (fun v => ∫ p,
      (observedRow beta (D n) r t v p - gaussianPosteriorResponse μ t r v p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t))) ∧
    Tendsto (fun n => ∑' v, ∫ p,
      (observedRow beta (D n) r t v p - gaussianPosteriorResponse μ t r v p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let q := Real.tanh beta ^ 2 * gaussianContraction beta t
  let X := fun n v => observedRow beta (D n) r t v
  let Y := fun v => gaussianPosteriorResponse μ t r v
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le
  have hqs : ((d - 1 : ℕ) : ℝ) * q < 1 := gaussian_radial_ratio_lt_one ht hcrit
  have hXm (n : ℕ) (v : TreeVertex d) : AEStronglyMeasurable (X n v) P :=
    (measurable_observedRow beta (D n) r t v).aestronglyMeasurable
  have hYm (v : TreeVertex d) : AEStronglyMeasurable (Y v) P :=
    ((stronglyMeasurable_posteriorResponse P (observationSigma (TreeVertex d) t)
      (fun p => spinSign (p.1 r)) (fun p => spinSign (p.1 v))).mono
        (observationSigma_le (TreeVertex d) t)).aestronglyMeasurable
  have hXi (n : ℕ) (v : TreeVertex d) : Integrable (fun p => X n v p ^ 2) P :=
    integrable_observedRow_sq μ hbeta t (hconn n) (hr n) hrnil v
  have hXb (n : ℕ) (v : TreeVertex d) : (∫ p, X n v p ^ 2 ∂P) ≤ q ^ v.1.length :=
    integral_observedRow_sq_le μ hbeta ht (hconn n) (hr n) hrnil v
  have hY (v : TreeVertex d) : Integrable (fun p => Y v p ^ 2) P ∧
      (∫ p, Y v p ^ 2 ∂P) ≤ q ^ v.1.length :=
    integrable_sq_and_integral_le_of_tendsto_ae P
      (fun n => hXm n v) (hYm v) (pow_nonneg hq _)
      (hμ.observedRow_tendsto_ae hbeta D hD hconn r hr hex t v)
      (Filter.Eventually.of_forall (fun n => ⟨hXi n v, hXb n v⟩))
  have hEi (n : ℕ) (v : TreeVertex d) :
      Integrable (fun p => (X n v p - Y v p) ^ 2) P := by
    exact (((memLp_two_iff_integrable_sq (hXm n v)).mpr (hXi n v)).sub
      ((memLp_two_iff_integrable_sq (hYm v)).mpr (hY v).1)).integrable_sq
  have hEb (n : ℕ) (v : TreeVertex d) :
      (∫ p, (X n v p - Y v p) ^ 2 ∂P) ≤ 4 * q ^ v.1.length := by
    have hle : (∫ p, (X n v p - Y v p) ^ 2 ∂P) ≤
        ∫ p, 2 * X n v p ^ 2 + 2 * Y v p ^ 2 ∂P := by
      apply integral_mono (hEi n v) (((hXi n v).const_mul 2).add ((hY v).1.const_mul 2))
      intro p
      change (X n v p - Y v p) ^ 2 ≤ 2 * X n v p ^ 2 + 2 * Y v p ^ 2
      nlinarith [sq_nonneg (X n v p + Y v p)]
    rw [integral_add ((hXi n v).const_mul 2) ((hY v).1.const_mul 2),
      integral_const_mul, integral_const_mul] at hle
    linarith [hXb n v, (hY v).2]
  have hs : Summable (fun v : TreeVertex d => 4 * q ^ v.1.length) :=
    (summable_geometric_radial d hq hqs).mul_left 4
  refine ⟨fun n => Summable.of_nonneg_of_le
    (fun v => integral_nonneg (fun p => sq_nonneg _)) (hEb n) hs, ?_⟩
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (fun v => hμ.observedRow_meanSquare hbeta D hD hconn r hr hex t v)
    (Filter.Eventually.of_forall (fun n v => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
      exact hEb n v))
  simpa only [tsum_zero] using hlim

end Problem367

end

end OAI
