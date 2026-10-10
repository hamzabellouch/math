import OAI.Probability.FreeIsing.Estimates.LinearEstimator
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianPosteriorNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteIsingBrownian_joint_law
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ≥0) :
    (μ.prod (Measure.infinitePi ν)).map
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        (D.restrict p.1, finiteIsingBrownianObservation B D t p)) =
    (μ.map D.restrict) ⊗ₘ finiteGaussianObservationKernel t
      (fun eta (v : D) => spinSign (eta v)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := inferInstance
  let spin : (D → IsingSpin) → D → ℝ := fun eta v => spinSign (eta v)
  have hr : MeasurePreserving D.restrict μ π := ⟨D.measurable_restrict, rfl⟩
  have hp := hr.prod (finiteBrownianNoise_restrict_measurePreserving ν hB hmB D t)
  let Y : (D → IsingSpin) × (D → ℝ) → (D → IsingSpin) × (D → ℝ) :=
    fun p => (p.1, fun v => (t : ℝ) * spin p.1 v + p.2 v)
  have hY : Measurable Y := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite (fun eta => spin eta v)).comp measurable_fst)).add
      ((measurable_pi_apply v).comp measurable_snd)
  have h := finiteGaussianPlanted_joint_law π t spin
  change Measure.map Y _ = _ at h
  rw [← hp.map_eq, Measure.map_map hY hp.measurable] at h
  unfold finiteIsingBrownianObservation
  simpa only [Y, spin, Function.comp_def, Prod.map_fst, Prod.map_snd,
    Finset.restrict, Real.toNNReal_coe] using h

theorem measurable_finiteIsingBrownianObservation
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ) :
    Measurable (finiteIsingBrownianObservation B D t) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_const.mul
    ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply (v : TreeVertex d)).comp measurable_fst))).add
    ((hmB v t.toNNReal).comp
      ((measurable_pi_apply (v : TreeVertex d)).comp measurable_snd))

theorem HasFreeIsingLaw.condExp_finiteIsingBrownian_observable
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    (t : ℝ≥0) (q : (D → IsingSpin) → ℝ) :
    let ρ := μ.prod (Measure.infinitePi ν)
    ρ[fun p => q (D.restrict p.1) |
      MeasurableSpace.comap (finiteIsingBrownianObservation B D t) inferInstance] =ᵐ[ρ]
      fun p => FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun eta (v : D) => spinSign (eta v)) q
        (finiteIsingBrownianObservation B D t p) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let : IsProbabilityMeasure (μ.map D.restrict) := inferInstance
  dsimp only
  exact FiniteBayes.condExp_state_eq_of_posterior_integral
    (μ.prod (Measure.infinitePi ν)) (μ.map D.restrict)
    (finiteGaussianObservationKernel t (fun eta (v : D) => spinSign (eta v)))
    (fun p => D.restrict p.1) (finiteIsingBrownianObservation B D t)
    (D.measurable_restrict.comp measurable_fst)
    (measurable_finiteIsingBrownianObservation hmB D t)
    (finiteIsingBrownian_joint_law μ ν hB hmB D t) q
    (FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta (v : D) => spinSign (eta v)) q)
    (hμ.gaussian_restrict_posterior_mean D hD t q)

abbrev brownianTerminalSigma {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ) :
    MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :=
  MeasurableSpace.comap
    (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      fun i => t * spinSign (p.1 i) + B i t.toNNReal (p.2 i)) inferInstance

theorem finiteIsingBrownianSigma_le_terminal
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (D : Finset (TreeVertex d)) (t : ℝ) :
    MeasurableSpace.comap (finiteIsingBrownianObservation B D t) inferInstance ≤
      brownianTerminalSigma B t := by
  have hr : Measurable (D.restrict : (TreeVertex d → ℝ) → D → ℝ) :=
    D.measurable_restrict
  have h := MeasurableSpace.comap_mono hr.comap_le
    (g := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      fun i => t * spinSign (p.1 i) + B i t.toNNReal (p.2 i))
  unfold finiteIsingBrownianObservation brownianTerminalSigma
  rw [MeasurableSpace.comap_comp] at h
  exact h

theorem brownianTerminalSigma_le
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ) :
    brownianTerminalSigma B t ≤
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) ×
        (TreeVertex d → Ω))) := by
  apply Measurable.comap_le
  apply Measurable.of_eval
  intro i
  exact (measurable_const.mul
    ((measurable_of_finite spinSign).comp
      ((measurable_pi_apply i).comp measurable_fst))).add
    ((hmB i t.toNNReal).comp ((measurable_pi_apply i).comp measurable_snd))

theorem HasFreeIsingLaw.finiteIsingBrownian_information_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    (t : ℝ≥0) :
    let ρ := μ.prod (Measure.infinitePi ν)
    (∫ p, finiteIsingBrownianMean beta D v B t p ^ 2 ∂ρ) ≤
      ∫ p, (ρ[fun z => spinSign (z.1 (v : TreeVertex d)) |
        brownianTerminalSigma B t] p) ^ 2 ∂ρ := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi ν)
  let signal : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) → ℝ :=
    fun p => spinSign (p.1 v)
  have hs : MemLp signal 2 ρ := by
    apply MemLp.of_bound
      (((measurable_of_finite spinSign).comp
        ((measurable_pi_apply (v : TreeVertex d)).comp measurable_fst)).aestronglyMeasurable) 1
    filter_upwards with p
    cases hp : p.1 v <;> norm_num [spinSign, hp]
  have hpost := hμ.condExp_finiteIsingBrownian_observable ν hB hmB D hD t
    (fun eta => spinSign (eta v))
  have heq : (∫ p, finiteIsingBrownianMean beta D v B t p ^ 2 ∂ρ) =
      ∫ p, (ρ[signal | MeasurableSpace.comap
        (finiteIsingBrownianObservation B D t) inferInstance] p) ^ 2 ∂ρ := by
    apply integral_congr_ae
    filter_upwards [hpost] with p hp
    exact congrArg (fun x : ℝ => x ^ 2) hp.symm
  dsimp only
  rw [heq]
  exact posterior_information_mono (finiteIsingBrownianSigma_le_terminal B D t)
    (brownianTerminalSigma_le hmB t) hs

theorem HasFreeIsingLaw.finiteIsingBrownian_energy_le_information
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    (T : ℝ≥0) :
    let ρ := μ.prod (Measure.infinitePi ν)
    (∫ t in (0 : ℝ)..(T : ℝ), ∫ p,
      ∑ u : D, finiteIsingBrownianCovariance beta D v u B t p ^ 2 ∂ρ) ≤
      ∫ p, (ρ[fun z => spinSign (z.1 (v : TreeVertex d)) |
        brownianTerminalSigma B T] p) ^ 2 ∂ρ := by
  have he := hμ.integral_finiteIsingBrownianEnergy ν hB hmB D hD v T.property
  dsimp only at he ⊢
  exact he.2.1.le.trans (hμ.finiteIsingBrownian_information_le ν hB hmB D hD v T)

end Problem367

end

end OAI
