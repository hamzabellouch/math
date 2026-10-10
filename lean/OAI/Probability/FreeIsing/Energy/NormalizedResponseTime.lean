import OAI.Probability.FreeIsing.Gaussian.BinaryPosteriorResponseBound
import OAI.Probability.FreeIsing.Posterior.NormalizedPosteriorRowConvergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.NormalizedResponseTime

open PlantedSymmetry GaussianTreeResponse

lemma observedRow_abs_le_one {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (v : TreeVertex d) (hv : v ∈ D) (t : ℝ) (w : TreeVertex d)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    |observedRow beta D v t w p| ≤ 1 := by
  classical
  by_cases hw : w ∈ D
  · simp only [observedRow, ite_eq_left hw]
    have hb := TreePathResponse.response_mem_Icc hbeta (observation t p) hD
      (⟨v, hv⟩ : D) (⟨w, hw⟩ : D)
    rw [abs_of_nonneg hb.1]
    exact hb.2.trans (pow_le_one₀ (tanh_nonneg_of_beta_nonneg hbeta)
      (Real.tanh_lt_one beta).le)
  · simp [observedRow, hw]

lemma infiniteGibbsResponse_eq_gaussianPosteriorResponse
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsResponse beta v w (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)] gaussianPosteriorResponse μ t v w := by
  filter_upwards [hμ.infiniteGibbsCovariance_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hc hm
  unfold infiniteGibbsResponse gaussianPosteriorResponse posteriorResponse
  rw [hc, hm]
  rfl

theorem observedRow_tendsto_ae_gaussian
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (w : TreeVertex d) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => observedRow beta (D n) v t w p) atTop
        (𝓝 (infiniteGibbsResponse beta v w (observation t p))) := by
  filter_upwards [hμ.observedRow_tendsto_ae hbeta D hD hconn v hv hex t w,
    infiniteGibbsResponse_eq_gaussianPosteriorResponse hμ t v w] with p hlim hinf
  rw [hinf]
  exact hlim

theorem observedRow_tendsto_ae_brownian
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (w : TreeVertex d) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Tendsto (fun n => observedRow beta (D n) v t w
        (p.1, fun i => B i t (p.2 i))) atTop
        (𝓝 (infiniteGibbsResponse beta v w
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have h := observedRow_tendsto_ae_gaussian hμ hbeta D hD hconn hex v hv w t
  rw [← hT.map_eq] at h
  exact ae_of_ae_map hT.measurable.aemeasurable h

theorem observedRow_time_meanSquare_brownian
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (w : TreeVertex d)
    (η : Measure ℝ≥0) [IsFiniteMeasure η] :
    Tendsto (fun n => ∫ q : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
      (observedRow beta (D n) v q.1 w
          (q.2.1, fun i => B i q.1 (q.2.2 i)) -
        infiniteGibbsResponse beta v w
          (fun i => (q.1 : ℝ) * spinSign (q.2.1 i) + B i q.1 (q.2.2 i))) ^ 2
        ∂η.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  have hs : Measurable spinSign := by intro s hs; trivial
  let Y : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      TreeVertex d → ℝ :=
    fun q i => (q.1 : ℝ) * spinSign (q.2.1 i) + B i q.1 (q.2.2 i)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_subtype_coe.comp measurable_fst).mul
      (hs.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
      ((hjoint i).comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))
  have hX (n : ℕ) : Measurable
      (fun q : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
        observedRow beta (D n) v q.1 w (q.2.1, fun i => B i q.1 (q.2.2 i))) := by
    classical
    by_cases hw : w ∈ D n
    · simp only [observedRow, ite_eq_left hw]
      change Measurable ((response beta (D n) v w) ∘ Y)
      exact (measurable_response beta (D n) v w).comp hY
    · simpa only [observedRow, ite_eq_right hw] using (measurable_const :
        Measurable (fun _ : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
          (0 : ℝ)))
  apply tendsto_integral_prod_sq_sub_of_bounded_ae η (μ.prod (Measure.infinitePi ν))
    hX ((measurable_infiniteGibbsResponse beta v w).comp hY) (by norm_num : (0 : ℝ) ≤ 1)
  · intro n
    apply Eventually.of_forall
    intro t
    apply Eventually.of_forall
    intro p
    exact observedRow_abs_le_one hbeta (D n) (hconn n) v (hv n) t w _
  · apply Eventually.of_forall
    intro t
    exact hμ.infiniteGibbsResponse_abs_le_one_brownian ν hB hmB t v w
  · apply Eventually.of_forall
    intro t
    exact observedRow_tendsto_ae_brownian hμ hbeta ν hB hmB D hD hconn hex v hv w t

end Problem367.NormalizedResponseTime

end

end OAI
