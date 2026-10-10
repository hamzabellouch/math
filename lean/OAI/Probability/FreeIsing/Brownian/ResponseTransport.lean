import OAI.Probability.FreeIsing.Brownian.PosteriorField
import OAI.Probability.FreeIsing.Posterior.NormalizedPosteriorLimit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open Filter
open scoped NNReal ENNReal Topology

namespace Problem367

open PlantedSymmetry

theorem posteriorResponse_comp_measurePreserving
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {T : Ω → Ξ} (hT : MeasurePreserving T μ ν)
    {f g : Ξ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hfgi : Integrable (fun x => f x * g x) ν)
    {m : MeasurableSpace Ξ} (hm : m ≤ mΞ) :
    posteriorResponse (mΩ := mΩ) μ (m.comap T) (f ∘ T) (g ∘ T) =ᵐ[μ]
      (posteriorResponse (mΩ := mΞ) ν m f g) ∘ T := by
  filter_upwards [condExp_comp_measurePreserving_comap (mΞ := mΞ)
      hT hf.stronglyMeasurable hfi hm,
    condExp_comp_measurePreserving_comap (mΞ := mΞ) hT hg.stronglyMeasurable hgi hm,
    condExp_comp_measurePreserving_comap (mΞ := mΞ)
      hT (hf.mul hg).stronglyMeasurable hfgi hm]
    with ω hfm hgm hfgm
  dsimp only [posteriorResponse, posteriorCovariance, Function.comp_def] at *
  simp only [Pi.mul_apply] at hfgm
  have heq : f * g = fun x => f x * g x := rfl
  rw [heq] at hfgm
  rw [hfm, hgm, hfgm]

theorem brownian_past_condExp_eq_gaussian_terminal
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0)
    (f : (TreeVertex d → IsingSpin) → ℝ) (hf : Measurable f)
    (hfi : Integrable f μ) :
    (μ.prod (Measure.infinitePi ν))[fun p => f p.1 |
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
        inferInstance] =ᵐ[μ.prod (Measure.infinitePi ν)]
      fun p => (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[fun p => f p.1 |
        observationSigma (TreeVertex d) t] (p.1, fun i => B i t (p.2 i)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun ω i => B i t (ω i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hsignal : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      fun i => spinSign (sigma i)) :=
    Measurable.of_eval (fun i => hsign.comp (measurable_pi_apply i))
  have hpast := TerminalSufficiency.condExp_planted_infinite_past_eq_terminal
    μ ν hB hmB (fun sigma i => spinSign (sigma i)) f hsignal hf hfi t
  have hpull := condExp_comp_measurePreserving_comap hT
    (hf.comp measurable_fst).stronglyMeasurable
    (hfi.comp_fst (gaussianNoiseLaw (TreeVertex d) t))
    (observationSigma_le (TreeVertex d) t)
  have hsame : (observationSigma (TreeVertex d) (t : ℝ)).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance := by
    rw [observationSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at hpull
  exact hpast.trans hpull

theorem brownian_past_posteriorResponse_eq_gaussian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v w : TreeVertex d) :
    posteriorResponse (μ.prod (Measure.infinitePi ν))
      (MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
        inferInstance)
      (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      fun p => gaussianPosteriorResponse μ t v w (p.1, fun i => B i t (p.2 i)) := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hspin (u : TreeVertex d) : Measurable (fun sigma : TreeVertex d → IsingSpin =>
      spinSign (sigma u)) := hsign.comp (measurable_pi_apply u)
  have hspini (u : TreeVertex d) : Integrable (fun sigma => spinSign (sigma u)) μ := by
    apply Integrable.of_bound (hspin u).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro sigma
    cases hs : sigma u <;> norm_num [spinSign, hs]
  have hpair : Integrable (fun sigma => spinSign (sigma v) * spinSign (sigma w)) μ := by
    apply Integrable.of_bound ((hspin v).mul (hspin w)).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro sigma
    cases hv : sigma v <;> cases hw : sigma w <;> norm_num [spinSign, hv, hw]
  filter_upwards [brownian_past_condExp_eq_gaussian_terminal μ ν hB hmB t
      (fun sigma => spinSign (sigma v)) (hspin v) (hspini v),
    brownian_past_condExp_eq_gaussian_terminal μ ν hB hmB t
      (fun sigma => spinSign (sigma w)) (hspin w) (hspini w),
    brownian_past_condExp_eq_gaussian_terminal μ ν hB hmB t
      (fun sigma => spinSign (sigma v) * spinSign (sigma w))
      ((hspin v).mul (hspin w)) hpair] with p hv hw hvw
  dsimp only [posteriorResponse, posteriorCovariance, gaussianPosteriorResponse]
  rw [hv, hw, hvw]

theorem brownian_finiteTerminal_posteriorResponse_eq_gaussian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0)
    (D : Finset (TreeVertex d)) (v w : TreeVertex d) :
    posteriorResponse (μ.prod (Measure.infinitePi ν))
      (MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i : D => (t : ℝ) * spinSign (p.1 i.1) + B i.1 t (p.2 i.1)) inferInstance)
      (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) =ᵐ[
        μ.prod (Measure.infinitePi ν)]
      fun p => posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation D t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w))
        (p.1, fun i => B i t (p.2 i)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    fun p => (p.1, fun i => B i t (p.2 i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hspin (u : TreeVertex d) : Measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => spinSign (p.1 u)) :=
    hsign.comp ((measurable_pi_apply u).comp measurable_fst)
  have hpair : Integrable (fun p => spinSign (p.1 v) * spinSign (p.1 w))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
    apply Integrable.of_bound ((hspin v).mul (hspin w)).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro p
    cases hv : p.1 v <;> cases hw : p.1 w <;> norm_num [spinSign, hv, hw]
  have h := posteriorResponse_comp_measurePreserving hT (hspin v) (hspin w)
    (integrable_plantedSpin _ v) (integrable_plantedSpin _ w) hpair
    (measurable_finiteObservation D t).comap_le
  have hsame : (MeasurableSpace.comap (finiteObservation D t) inferInstance).comap T =
      MeasurableSpace.comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun i : D => (t : ℝ) * spinSign (p.1 i.1) + B i.1 t (p.2 i.1)) inferInstance := by
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [hsame] at h
  exact h

theorem HasFreeIsingLaw.brownian_posteriorResponse_meanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d) :
    Tendsto (fun n => ∫ p,
      (posteriorResponse (μ.prod (Measure.infinitePi ν))
        (MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i : D n => (t : ℝ) * spinSign (p.1 i.1) + B i.1 t (p.2 i.1)) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p -
       posteriorResponse (μ.prod (Measure.infinitePi ν))
        (MeasurableSpace.comap
          (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
            fun i (s : Set.Iic t) => (s.1 : ℝ) * spinSign (p.1 i) + B i s.1 (p.2 i))
          inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) ^ 2
      ∂μ.prod (Measure.infinitePi ν)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    fun p => (p.1, fun i => B i t (p.2 i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hlim := hμ.gaussian_posteriorResponse_meanSquare hbeta D hD hex t v w
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro n
  symm
  calc
    _ = ∫ p,
        (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
          (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) (T p) -
          gaussianPosteriorResponse μ t v w (T p)) ^ 2 ∂μ.prod (Measure.infinitePi ν) := by
      apply integral_congr_ae
      filter_upwards [brownian_finiteTerminal_posteriorResponse_eq_gaussian
          μ ν hB hmB t (D n) v w,
        brownian_past_posteriorResponse_eq_gaussian μ ν hB hmB t v w] with p hn hfull
      rw [hn, hfull]
    _ = _ := hT.hasLaw.integral_comp
      ((((stronglyMeasurable_posteriorResponse _ _ _ _).mono
        (measurable_finiteObservation (D n) t).comap_le).sub
        ((stronglyMeasurable_posteriorResponse _ _ _ _).mono
          (observationSigma_le (TreeVertex d) t))).pow 2).aestronglyMeasurable

end Problem367

end

end OAI
