import OAI.Probability.FreeIsing.Posterior.FieldMoments
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.identDistrib_brownianGibbsField
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    IdentDistrib
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        Real.artanh (infiniteGibbsSpinMean beta v
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))))
      (gaussianPosteriorField μ t v)
      (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hF := measurable_gaussianPosteriorField μ t v
  have hlaw : IdentDistrib (gaussianPosteriorField μ t v ∘ T)
      (gaussianPosteriorField μ t v) (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
    refine ⟨(hF.comp hT.measurable).aemeasurable, hF.aemeasurable, ?_⟩
    rw [← Measure.map_map hF hT.measurable, hT.map_eq]
  have heq := hT.quasiMeasurePreserving.ae_eq_comp
    ((hμ.infiniteGibbsSpinMean_eq_posterior t v).fun_comp Real.artanh)
  have heq' : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      Real.artanh (infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) =ᵐ[
      μ.prod (Measure.infinitePi ν)] gaussianPosteriorField μ t v ∘ T := by
    filter_upwards [heq] with q hq
    exact hq
  exact (IdentDistrib.of_ae_eq hlaw.aemeasurable_fst heq'.symm).symm.trans hlaw

theorem HasFreeIsingLaw.integrable_brownianGibbsField_abs_pow
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) (p : ℕ) :
    Integrable
      (fun q : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        |Real.artanh (infiniteGibbsSpinMean beta v
          (fun i => (t : ℝ) * spinSign (q.1 i) + B i t (q.2 i)))| ^ p)
      (μ.prod (Measure.infinitePi ν)) := by
  have h := (hμ.identDistrib_brownianGibbsField ν hB hmB t v).comp
    (u := fun x : ℝ => |x| ^ p) (by fun_prop)
  exact h.integrable_iff.mpr (hμ.integrable_gaussianPosteriorField_abs_pow hbeta t v p)

theorem HasFreeIsingLaw.memLp_brownianGibbsField_two
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    MemLp
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        Real.artanh (infiniteGibbsSpinMean beta v
          (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))))
      2 (μ.prod (Measure.infinitePi ν)) :=
  (hμ.identDistrib_brownianGibbsField ν hB hmB t v).memLp_iff.mpr
    (hμ.memLp_gaussianPosteriorField_two hbeta t v)

theorem HasFreeIsingLaw.brownianGibbsField_second_moment_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      (Real.artanh (infiniteGibbsSpinMean beta v
        (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)))) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤
      2 * ((t : ℝ) + ((d : ℝ) * beta + t) ^ 2) := by
  have h := (hμ.identDistrib_brownianGibbsField ν hB hmB t v).comp
    (u := fun x : ℝ => x ^ 2) (by fun_prop)
  exact h.integral_eq.trans_le (hμ.gaussianPosteriorField_second_moment_le hbeta t v)

end Problem367

end

end OAI
