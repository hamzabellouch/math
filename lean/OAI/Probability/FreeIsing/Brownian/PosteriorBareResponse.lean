import OAI.Probability.FreeIsing.Brownian.ResponseTransport
import OAI.Probability.FreeIsing.Gaussian.PosteriorBareResponse

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry

def brownianPosteriorResponse {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) (ν : TreeVertex d → Measure Ω)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (u v : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) → ℝ :=
  posteriorResponse (μ.prod (Measure.infinitePi ν))
    (MeasurableSpace.comap
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
      inferInstance)
    (fun p => spinSign (p.1 u)) (fun p => spinSign (p.1 v))

theorem HasFreeIsingLaw.brownian_posteriorResponse_mem_Icc
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (u v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      brownianPosteriorResponse μ ν B t u v p ∈
        Set.Icc 0 (Real.tanh beta ^ reducedWordDistance u.1 v.1) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hT := (MeasurePreserving.id μ).prod
    (brownian_array_eval_measurePreserving ν hB hmB t)
  have hbound := hT.quasiMeasurePreserving.ae
    (hμ.gaussian_posteriorResponse_mem_Icc hbeta t u v)
  filter_upwards [brownian_past_posteriorResponse_eq_gaussian μ ν hB hmB t u v,
    hbound] with p hp hb
  change brownianPosteriorResponse μ ν B t u v p = _ at hp
  rw [hp]
  exact hb

theorem HasFreeIsingLaw.brownian_posteriorResponse_row_bound_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (u : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (Measure.infinitePi ν),
      Summable (fun v => brownianPosteriorResponse μ ν B t u v p ^ 2) ∧
      (∑' v, brownianPosteriorResponse μ ν B t u v p ^ 2) ≤
        1 + (d : ℝ) * Real.tanh beta ^ 2 /
          (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) ∧
      ∀ L : ℕ, (∑' v : TreeVertex d, if L < reducedWordDistance u.1 v.1
        then brownianPosteriorResponse μ ν B t u v p ^ 2 else 0) ≤
          (d : ℝ) * Real.tanh beta ^ 2 *
            (((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) ^ L /
            (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hT := (MeasurePreserving.id μ).prod
    (brownian_array_eval_measurePreserving ν hB hmB t)
  have hbound := hT.quasiMeasurePreserving.ae
    (hμ.gaussian_posteriorResponse_row_bound_of_strict hbeta hstrict t u)
  have heq := (ae_all_iff).2
    (fun v => brownian_past_posteriorResponse_eq_gaussian μ ν hB hmB t u v)
  filter_upwards [heq, hbound] with p hp hb
  have he (v : TreeVertex d) : brownianPosteriorResponse μ ν B t u v p =
      gaussianPosteriorResponse μ t u v (p.1, fun i => B i t (p.2 i)) := hp v
  simp_rw [he]
  exact hb

theorem HasFreeIsingLaw.brownian_posteriorResponse_integrable_energy_of_strict
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hstrict : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 < 1)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (u : TreeVertex d) :
    Integrable (fun p => ∑' v, brownianPosteriorResponse μ ν B t u v p ^ 2)
      (μ.prod (Measure.infinitePi ν)) ∧
    (∫ p, ∑' v, brownianPosteriorResponse μ ν B t u v p ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤
        1 + (d : ℝ) * Real.tanh beta ^ 2 /
          (1 - ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hT := (MeasurePreserving.id μ).prod
    (brownian_array_eval_measurePreserving ν hB hmB t)
  have hg := hμ.gaussian_posteriorResponse_integrable_energy_of_strict hbeta hstrict t u
  have heq := (ae_all_iff).2
    (fun v => brownian_past_posteriorResponse_eq_gaussian μ ν hB hmB t u v)
  have he : (fun p => ∑' v, brownianPosteriorResponse μ ν B t u v p ^ 2) =ᵐ[
      μ.prod (Measure.infinitePi ν)]
      (fun q => ∑' v, gaussianPosteriorResponse μ t u v q ^ 2) ∘
        Prod.map id (fun p i => B i t (p i)) := by
    filter_upwards [heq] with p hp
    apply tsum_congr
    intro v
    exact congrArg (fun x : ℝ => x ^ 2) (hp v)
  refine ⟨(hT.integrable_comp_of_integrable hg.1).congr he.symm, ?_⟩
  rw [integral_congr_ae he, hT.hasLaw.integral_comp hg.1.aestronglyMeasurable]
  exact hg.2

end Problem367

end

end OAI
