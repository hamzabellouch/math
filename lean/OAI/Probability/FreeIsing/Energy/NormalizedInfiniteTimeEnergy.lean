import OAI.Probability.FreeIsing.Brownian.EntropyEnergy
import OAI.Probability.FreeIsing.Energy.NormalizedResponseEnergy
import OAI.Probability.FreeIsing.Energy.NormalizedResponseTime

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Problem367.NormalizedInfiniteTimeEnergy

open GaussianTreeResponse

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def observation (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : TreeVertex d → ℝ :=
  fun i => t * spinSign (p.1 i) + B i t.toNNReal (p.2 i)

def finiteRow (beta : ℝ) (D : Finset (TreeVertex d)) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (w : TreeVertex d)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  observedRow beta D v q.1 w (q.2.1, fun i => B i q.1.toNNReal (q.2.2 i))

def infiniteRow (beta : ℝ) (v : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (w : TreeVertex d)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) : ℝ :=
  infiniteGibbsResponse beta v w
    (fun i => q.1 * spinSign (q.2.1 i) + B i q.1.toNNReal (q.2.2 i))

lemma measurable_observation
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2)) :
    Measurable (fun q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
      observation B q.1 q.2) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_fst.mul ((measurable_of_finite spinSign).comp
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))).add
    ((hjoint i).comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))

lemma measurable_finiteRow (beta : ℝ) (D : Finset (TreeVertex d))
    (v : TreeVertex d) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (w : TreeVertex d) : Measurable (finiteRow beta D v B w) := by
  classical
  by_cases hw : w ∈ D
  · unfold finiteRow
    simp only [observedRow, ite_eq_left hw]
    exact (measurable_response beta D v w).comp (measurable_observation hjoint)
  · unfold finiteRow
    simp only [observedRow, ite_eq_right hw]
    exact measurable_const

lemma measurable_infiniteRow (beta : ℝ) (v : TreeVertex d)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (w : TreeVertex d) : Measurable (infiniteRow beta v B w) :=
  (measurable_infiniteGibbsResponse beta v w).comp (measurable_observation hjoint)

omit [MeasurableSpace Ω] in

lemma finiteRow_eq_normalizedCovariance (beta : ℝ) (D : Finset (TreeVertex d))
    (v w : D) (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :
    finiteRow beta D v B w (t, p) =
      finiteIsingBrownianNormalizedCovariance beta D v w B t p := by
  classical
  simp only [finiteRow, observedRow, ite_eq_left w.property]
  unfold response TreePathResponse.response TreePathResponse.covariance
    LeafGibbs.covariance TreePathResponse.mean
    finiteIsingBrownianNormalizedCovariance FinitePosterior.normalizedFieldCovariance
    FinitePosterior.fieldCovariance
  simp only [extendFiniteSpin_apply D _ v, extendFiniteSpin_apply D _ w,
    GibbsLeaf.expectation_eq_fieldMean]
  rfl

omit [MeasurableSpace Ω] in
lemma finiteRow_eq_zero (beta : ℝ) (D : Finset (TreeVertex d)) (v w : TreeVertex d)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hw : w ∉ D)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
    finiteRow beta D v B w q = 0 := by
  simp [finiteRow, observedRow, hw]

omit [MeasurableSpace Ω] in
lemma tsum_finiteRow_sq (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω))) :
    (∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2)) =
      ENNReal.ofReal (∑ w : D,
        finiteIsingBrownianNormalizedCovariance beta D v w B q.1 q.2 ^ 2) := by
  classical
  rcases q with ⟨t, p⟩
  rw [tsum_eq_sum (s := D)]
  · rw [← Finset.sum_coe_sort D]
    simp_rw [finiteRow_eq_normalizedCovariance]
    exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
  · intro w hw
    simp [finiteRow_eq_zero beta D v w B hw]

theorem finiteRow_tendsto_ae
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (w : TreeVertex d) (T : ℝ) :
    ∀ᵐ q ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν)),
      Tendsto (fun n => finiteRow beta (D n) v B w q) atTop
        (𝓝 (infiniteRow beta v B w q)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun
    (fun n => measurable_finiteRow beta (D n) v hjoint w)
    (measurable_infiniteRow beta v hjoint w))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have h := NormalizedResponseTime.observedRow_tendsto_ae_brownian
    hμ hbeta ν hB hmB D hD hconn hex v hv w t.toNNReal
  simpa only [finiteRow, infiniteRow, Real.coe_toNNReal t ht.1.le] using h

theorem lintegral_infiniteRow_le_of_finite
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v : TreeVertex d) (hv : ∀ n, v ∈ D n) (T : ℝ) {K : ℝ≥0∞}
    (henergy : ∀ n,
      (∫⁻ q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
        ∑ u : D n, ENNReal.ofReal
          (finiteIsingBrownianNormalizedCovariance beta (D n) ⟨v, hv n⟩ u B q.1 q.2 ^ 2)
        ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤ K) :
    (∫⁻ q, ∑' w, ENNReal.ofReal (infiniteRow beta v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤ K := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  let P := (volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))
  rw [lintegral_tsum (fun w =>
    ((measurable_infiniteRow beta v hjoint w).pow_const 2).ennreal_ofReal.aemeasurable)]
  apply tsum_lintegral_sq_le_of_ae_tendsto P
    (fun n w => (measurable_finiteRow beta (D n) v hjoint w).aestronglyMeasurable)
    (fun w => finiteRow_tendsto_ae hμ hbeta ν hB hmB hjoint D hD hconn hex v hv w T)
  intro n
  rw [← lintegral_tsum (fun w =>
    ((measurable_finiteRow beta (D n) v hjoint w).pow_const 2).ennreal_ofReal.aemeasurable)]
  calc
    _ = ∫⁻ q : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
        ∑ u : D n, ENNReal.ofReal
          (finiteIsingBrownianNormalizedCovariance beta (D n) ⟨v, hv n⟩ u B q.1 q.2 ^ 2)
        ∂P := by
      apply lintegral_congr
      intro q
      rw [tsum_finiteRow_sq beta (D n) ⟨v, hv n⟩ B q]
      exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)
    _ ≤ K := henergy n

theorem lintegral_infiniteRow_le
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ q, ∑' w, ENNReal.ofReal (infiniteRow beta v B w q ^ 2)
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤
      ENNReal.ofReal (2 * ((d : ℝ) * beta + T + Real.sqrt T)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  apply lintegral_infiniteRow_le_of_finite hμ hbeta ν hB hmB hjoint
    (connectedExhaustion v) (connectedExhaustion_monotone v)
    (connectedExhaustion_connected v)
    (fun u => (eventually_mem_connectedExhaustion v u).exists)
    v (mem_connectedExhaustion v) T
  intro n
  let D := connectedExhaustion v n
  let r : D := ⟨v, mem_connectedExhaustion v n⟩
  let R : ℝ × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (∑ u : D,
      finiteIsingBrownianNormalizedCovariance beta D r u B q.1 q.2 ^ 2)
  have hR : Measurable R := by
    have heq : R = fun q => ∑' w, ENNReal.ofReal (finiteRow beta D v B w q ^ 2) := by
      funext q
      exact (tsum_finiteRow_sq beta D r B q).symm
    rw [heq]
    exact Measurable.tsum (fun w =>
      ((measurable_finiteRow beta D v hjoint w).pow_const 2).ennreal_ofReal)
  calc
    _ = ∫⁻ q, R q
        ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν)) := by
      apply lintegral_congr
      intro q
      exact (ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)).symm
    _ = ∫⁻ t in Ioc 0 T, ∫⁻ p, R (t, p) ∂μ.prod (Measure.infinitePi ν) :=
      lintegral_prod R hR.aemeasurable
    _ ≤ _ := hμ.lintegral_finiteIsingBrownianNormalizedEnergy_le hbeta ν hB hmB
      D (connectedExhaustion_connected v n) r hT

theorem row_energy_integrable
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    (∀ᵐ q ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν)),
      Summable (fun w => infiniteRow beta v B w q ^ 2)) ∧
    Integrable (fun q => ∑' w, infiniteRow beta v B w q ^ 2)
      ((volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ∧
    (∫ q, ∑' w, infiniteRow beta v B w q ^ 2
      ∂(volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))) ≤
      2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  let P := (volume.restrict (Ioc 0 T)).prod (μ.prod (Measure.infinitePi ν))
  have henergy := lintegral_infiniteRow_le hμ hbeta ν hB hmB hjoint v hT
  rw [lintegral_tsum (fun w =>
    ((measurable_infiniteRow beta v hjoint w).pow_const 2).ennreal_ofReal.aemeasurable)] at henergy
  have hm (w : TreeVertex d) : AEStronglyMeasurable (infiniteRow beta v B w) P :=
    (measurable_infiniteRow beta v hjoint w).aestronglyMeasurable
  exact ⟨ae_summable_sq_of_tsum_lintegral_sq_ne_top P hm
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top henergy),
    integral_tsum_sq_le_of_tsum_lintegral_sq_le P hm (by positivity) henergy⟩

theorem ae_path_row_energy_integrable
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      IntervalIntegrable (fun t => ∑' w, infiniteRow beta v B w (t, p) ^ 2)
        volume 0 T := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  filter_upwards [(row_energy_integrable hμ hbeta ν hB hmB hjoint v hT).2.1.prod_left_ae]
    with p hp
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hp

theorem integral_mean_row_energy_le
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hjoint : ∀ i, Measurable (fun z : ℝ≥0 × Ω => B i z.1 z.2))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => ∫ p, ∑' w, infiniteRow beta v B w (t, p) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) volume 0 T ∧
    (∫ t in 0..T, ∫ p, ∑' w, infiniteRow beta v B w (t, p) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤ 2 * ((d : ℝ) * beta + T + Real.sqrt T) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (vertex : TreeVertex d) : IsProbabilityMeasure (ν vertex) :=
    (hB vertex).isGaussianProcess.isProbabilityMeasure
  have h := row_energy_integrable hμ hbeta ν hB hmB hjoint v hT
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
    h.2.1.integral_prod_left, ?_⟩
  rw [intervalIntegral.integral_of_le hT, ← integral_prod _ h.2.1]
  exact h.2.2

end Problem367.NormalizedInfiniteTimeEnergy

end

end OAI
