import OAI.Probability.FreeIsing.Gibbs.CovarianceIntrinsicEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367

open PlantedSymmetry GaussianTreeCovariance

theorem integral_brownian_ising_observation_eq_gaussian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0)
    (f : (TreeVertex d → ℝ) → ℝ) (hf : Measurable f) :
    (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      f (fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i))
      ∂μ.prod (Measure.infinitePi ν)) =
      ∫ p, f (observation t p) ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    Prod.map id (fun omega i => B i t (omega i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hL : HasLaw T (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (μ.prod (Measure.infinitePi ν)) := ⟨hT.measurable.aemeasurable, hT.map_eq⟩
  exact hL.integral_comp ((hf.comp (measurable_observation t)).aestronglyMeasurable)

theorem HasFreeIsingLaw.integral_covarianceError_time_le
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] {δ : ℝ≥0} (hδ : 0 < δ)
    (hτ : ∀ᵐ t ∂τ, δ ≤ t) (v w : TreeVertex d) (n : ℕ) :
    (∫ p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
      (finiteGibbsCovariance beta v w n
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)) -
        infiniteGibbsCovariance beta v w
          (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i))) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) ≤
      (4 * τ.real Set.univ) *
        (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ reducedWordDistance v.1 w.1 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hi := integrable_finiteGibbsCovariance_sub_infinite_sq beta v w n
    (P := τ.prod (μ.prod (Measure.infinitePi ν)))
    (measurable_brownian_ising_observation_uncurry hmB hcB)
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _t, (4 * (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ reducedWordDistance v.1 w.1) ∂τ := by
      apply integral_mono_ae hi.integral_prod_left (integrable_const _)
      filter_upwards [hτ] with t ht
      rw [integral_brownian_ising_observation_eq_gaussian μ ν hB hmB t
        (fun y => (finiteGibbsCovariance beta v w n y -
          infiniteGibbsCovariance beta v w y) ^ 2)
        (((continuous_finiteGibbsCovariance beta v w n).measurable.sub
          (measurable_infiniteGibbsCovariance beta v w)).pow_const 2)]
      exact hμ.integral_finiteGibbsCovariance_sub_infinite_sq_le_distance hb hδ ht v w n
    _ = _ := by
      rw [integral_const]
      simp only [smul_eq_mul]
      ring

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_timeRowMeanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] {δ : ℝ≥0} (hδ : 0 < δ)
    (hτ : ∀ᵐ t ∂τ, δ ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) :
    Tendsto (fun n => ∑' w,
      ∫ p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)),
        (finiteGibbsCovariance beta v w n
            (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)) -
          infiniteGibbsCovariance beta v w
            (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i))) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  have hs := (summable_geometric_intrinsic v
    (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
    (gaussian_radial_ratio_lt_one hδ hcrit)).mul_left (4 * τ.real Set.univ)
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (fun w => hμ.finiteGibbsCovariance_brownian_tendsto_timeMeanSquare ν hB hmB hcB τ v w)
    (Eventually.of_forall fun n w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun p => sq_nonneg _))]
      exact hμ.integral_covarianceError_time_le hb ν hB hmB hcB τ hδ hτ v w n)
  simpa only [tsum_zero] using hlim

theorem HasFreeIsingLaw.finiteGibbsCovariance_brownian_tendsto_integral_timeRowMeanSquare
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (τ : Measure ℝ≥0) [IsFiniteMeasure τ] {δ : ℝ≥0} (hδ : 0 < δ)
    (hτ : ∀ᵐ t ∂τ, δ ≤ t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) :
    Tendsto (fun n =>
      ∫ p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)), ∑' w,
        (finiteGibbsCovariance beta v w n
            (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)) -
          infiniteGibbsCovariance beta v w
            (fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i))) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let X := fun p : ℝ≥0 × ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) =>
    fun i => (p.1 : ℝ) * spinSign (p.2.1 i) + B i p.1 (p.2.2 i)
  have heq (n : ℕ) :
      (∫ p, ∑' w, (finiteGibbsCovariance beta v w n (X p) -
        infiniteGibbsCovariance beta v w (X p)) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi ν))) =
      ∑' w, ∫ p, (finiteGibbsCovariance beta v w n (X p) -
        infiniteGibbsCovariance beta v w (X p)) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi ν)) := by
    apply (integral_tsum_of_summable_integral_norm
      (fun w => integrable_finiteGibbsCovariance_sub_infinite_sq beta v w n
        (measurable_brownian_ising_observation_uncurry hmB hcB)) _).symm
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact Summable.of_nonneg_of_le
      (fun w => integral_nonneg (fun p => sq_nonneg _))
      (fun w => hμ.integral_covarianceError_time_le hb ν hB hmB hcB τ hδ hτ v w n)
      ((summable_geometric_intrinsic v
        (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)
        (gaussian_radial_ratio_lt_one hδ hcrit)).mul_left (4 * τ.real Set.univ))
  change Tendsto (fun n => ∫ p, ∑' w,
    (finiteGibbsCovariance beta v w n (X p) - infiniteGibbsCovariance beta v w (X p)) ^ 2
      ∂τ.prod (μ.prod (Measure.infinitePi ν))) atTop (𝓝 0)
  simp_rw [heq]
  exact hμ.finiteGibbsCovariance_brownian_tendsto_timeRowMeanSquare
    hb ν hB hmB hcB τ hδ hτ hcrit v

end Problem367

end

end OAI
