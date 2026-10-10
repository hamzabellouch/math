import OAI.Probability.FreeIsing.Ising.CopyCavityBounds
import OAI.Probability.FreeIsing.Ising.ObservationComparison

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCopyPathBounds

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def edgeLogDifference (hbeta : 0 ≤ beta) (t : ℝ≥0) (v w : TreeVertex d)
    (q : IsingConditionalCopyBounds.CopySpace d) : ℝ :=
  Real.log (responseAttenuation (Real.tanh beta)
    (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (sitePair beta t q).1 v w)) -
  Real.log (responseAttenuation (Real.tanh beta)
    (CavityArray.field (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (sitePair beta t q).2 v w))

def edgeLogBound (d : ℕ) (beta : ℝ) (T : ℝ≥0) : ℝ :=
  2 * ((2 * (T : ℝ) + 2 * (d : ℝ) * beta) / (1 - Real.tanh beta))

theorem edgeLogBound_nonneg (hbeta : 0 ≤ beta) (T : ℝ≥0) :
    0 ≤ edgeLogBound d beta T := by
  have hden : 0 < 1 - Real.tanh beta := sub_pos.mpr (Real.tanh_lt_one beta)
  unfold edgeLogBound
  positivity

theorem measurable_edgeLogDifference (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (v w : TreeVertex d) : Measurable (edgeLogDifference hbeta t v w) := by
  have h0 := tanh_nonneg_of_beta_nonneg hbeta
  have h1 := Real.tanh_lt_one beta
  have hs : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  have hl := (lipschitzWith_log_responseAttenuation hs).continuous.measurable
  have hc := CavityArray.measurable_field_apply h0 h1 v w
  exact (hl.comp (hc.comp (measurable_fst.comp (measurable_sitePair beta t)))).sub
    (hl.comp (hc.comp (measurable_snd.comp (measurable_sitePair beta t))))

theorem ae_all_siteDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) :
    ∀ᵐ q ∂copies beta μ, ∀ v : TreeVertex d,
      |(sitePair beta t q).1 v - (sitePair beta t q).2 v| ≤
        2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  apply ae_all_iff.mpr
  intro v
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    inferInstance
  have h := IsingConditionalCopyBounds.ae_fieldDifference_bound hμ hbeta
    kernel_graphLaw t v
  filter_upwards [h] with q hq
  have ht' : (t : ℝ) ≤ (T : ℝ) := ht
  exact hq.trans (by linarith)

theorem ae_edgeLogDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (v w : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      |edgeLogDifference hbeta t v w q| ≤ edgeLogBound d beta T := by
  have h0 := tanh_nonneg_of_beta_nonneg hbeta
  have h1 := Real.tanh_lt_one beta
  have hs : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  filter_upwards [ae_all_siteDifference_bound hμ hbeta ht] with q hq
  have hc := CavityArray.field_sub_abs_le h0 h1 v w (hq v) (hq w)
  have hl := (lipschitzWith_log_responseAttenuation hs).dist_le_mul
    (CavityArray.field h0 h1 (sitePair beta t q).1 v w)
    (CavityArray.field h0 h1 (sitePair beta t q).2 v w)
  apply (show |edgeLogDifference hbeta t v w q| ≤
    2 * |CavityArray.field h0 h1 (sitePair beta t q).1 v w -
      CavityArray.field h0 h1 (sitePair beta t q).2 v w| from by
        simpa only [edgeLogDifference, Real.dist_eq, NNReal.coe_ofNat] using hl).trans
  exact mul_le_mul_of_nonneg_left hc (by norm_num)

def pathLogDifference {ι : Type*} (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (q : IsingConditionalCopyBounds.CopySpace d) : ℝ :=
  ∑ i ∈ s, edgeLogDifference hbeta t (e i).1 (e i).2 q

theorem measurable_pathLogDifference {ι : Type*}
    (hbeta : 0 ≤ beta) (t : ℝ≥0) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    Measurable (pathLogDifference hbeta t s e) :=
  Finset.measurable_fun_sum s (fun i _ =>
    measurable_edgeLogDifference hbeta t (e i).1 (e i).2)

theorem ae_pathLogDifference_bound {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      |pathLogDifference hbeta t s e q| ≤ (s.card : ℝ) * edgeLogBound d beta T := by
  classical
  have hall : ∀ᵐ q ∂copies beta μ, ∀ i ∈ s,
      |edgeLogDifference hbeta t (e i).1 (e i).2 q| ≤ edgeLogBound d beta T :=
    (ae_ball_iff s.finite_toSet.countable).mpr (fun i _ =>
      ae_edgeLogDifference_bound hμ hbeta ht (e i).1 (e i).2)
  filter_upwards [hall] with q hq
  calc
    |pathLogDifference hbeta t s e q| ≤
        ∑ i ∈ s, |edgeLogDifference hbeta t (e i).1 (e i).2 q| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, edgeLogBound d beta T := Finset.sum_le_sum hq
    _ = (s.card : ℝ) * edgeLogBound d beta T := by simp

theorem ae_pathLogDifference_sq_bound {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      pathLogDifference hbeta t s e q ^ 2 ≤
        (s.card : ℝ) ^ 2 * edgeLogBound d beta T ^ 2 := by
  filter_upwards [ae_pathLogDifference_bound hμ hbeta ht s e] with q hq
  have hb : 0 ≤ (s.card : ℝ) * edgeLogBound d beta T :=
    mul_nonneg (Nat.cast_nonneg _) (edgeLogBound_nonneg hbeta T)
  simpa only [sq_abs, mul_pow] using (sq_le_sq₀ (abs_nonneg _) hb).mpr hq

theorem memLp_pathLogDifference {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d)
    (p : ℝ≥0∞) : MemLp (pathLogDifference hbeta t s e) p (copies beta μ) := by
  apply MemLp.of_bound (measurable_pathLogDifference hbeta t s e).aestronglyMeasurable
    ((s.card : ℝ) * edgeLogBound d beta t)
  simpa only [Real.norm_eq_abs] using ae_pathLogDifference_bound hμ hbeta le_rfl s e

theorem integrable_pathLogDifference_sq {ι : Type*}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (s : Finset ι) (e : ι → TreeVertex d × TreeVertex d) :
    Integrable (fun q => pathLogDifference hbeta t s e q ^ 2) (copies beta μ) :=
  (memLp_pathLogDifference hμ hbeta t s e 2).integrable_sq

end Problem367.IsingCopyPathBounds

end

end OAI
