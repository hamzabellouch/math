import OAI.Probability.FreeIsing.Ising.MixedFiltering

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

lemma measurable_finiteCovariance_joint
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (n : ℕ) :
    Measurable (Function.uncurry (finiteCovariance beta B v u n)) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · exact finiteCovariance_continuous beta B hcB v u n
  · intro t
    exact ((finiteCovariance_stronglyAdapted beta B hmB v u n t).mono
      ((ArrayPosteriorStationarity.filtration B hmB).le t)).measurable

theorem finiteCovariance_tendsto_ae
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (t : ℝ≥0) (v u : TreeVertex d) :
    ∀ᵐ q ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      Tendsto (fun n => finiteCovariance beta B v u n t q) atTop
        (𝓝 (covariance beta B v u t q)) := by
  simpa only [finiteCovariance, covariance, plantedArrayObservation,
    ArrayPosteriorStationarity.spinArray, add_comm] using
    hμ.finiteGibbsCovariance_brownian_tendsto_ae
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t v u

theorem finiteCovariance_tendsto_finiteMeasureMeanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (τ : Measure ℝ) [IsFiniteMeasure τ] (v u : TreeVertex d) :
    Tendsto (fun n => ∫ p : ℝ × State d A,
      (finiteCovariance beta B v u n p.1.toNNReal p.2 -
        covariance beta B v u p.1.toNNReal p.2) ^ 2
        ∂τ.prod (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun p : ℝ × State d A => (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  apply tendsto_integral_prod_sq_sub_of_bounded_ae τ
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (fun n => (measurable_finiteCovariance_joint beta B hmB hcB v u n).comp hm)
    ((measurable_covariance_joint beta B hmB hcB v u).comp hm)
    (by norm_num : (0 : ℝ) ≤ 2)
  · intro n
    exact Eventually.of_forall fun t => Eventually.of_forall fun q =>
      by simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
        finiteCovariance_abs_le_two beta B v u n t.toNNReal q
  · exact Eventually.of_forall fun t => Eventually.of_forall fun q =>
      by simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
        covariance_abs_le_two beta B v u t.toNNReal q
  · exact Eventually.of_forall fun t =>
      finiteCovariance_tendsto_ae hμ ν hB hmB t.toNNReal v u

theorem finiteCovariance_tendsto_timeMeanSquare
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v u : TreeVertex d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p : ℝ × State d A,
      (finiteCovariance beta B v u n p.1.toNNReal p.2 -
        covariance beta B v u p.1.toNNReal p.2) ^ 2
        ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
          (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
      atTop (𝓝 0) := by
  exact finiteCovariance_tendsto_finiteMeasureMeanSquare hμ ν hB hmB hcB _ v u

lemma memLp_finiteCovariance_time
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a))
    (P : Measure (State d A)) [IsFiniteMeasure P]
    (τ : Measure ℝ) [IsFiniteMeasure τ] (v u : TreeVertex d) (n : ℕ) :
    MemLp (fun p : ℝ × State d A =>
      finiteCovariance beta B v u n p.1.toNNReal p.2) 2 (τ.prod P) := by
  apply MemLp.of_bound
    ((measurable_finiteCovariance_joint beta B hmB hcB v u n).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
    2
  exact Eventually.of_forall fun p => by
    simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
      finiteCovariance_abs_le_two beta B v u n p.1.toNNReal p.2

lemma memLp_covariance_time
    (beta : ℝ) (B : ℝ≥0 → A → ℝ) (hmB : ∀ t, Measurable (B t))
    (hcB : ∀ a, Continuous (fun t => B t a))
    (P : Measure (State d A)) [IsFiniteMeasure P]
    (τ : Measure ℝ) [IsFiniteMeasure τ] (v u : TreeVertex d) :
    MemLp (fun p : ℝ × State d A =>
      covariance beta B v u p.1.toNNReal p.2) 2 (τ.prod P) := by
  apply MemLp.of_bound
    ((measurable_covariance_joint beta B hmB hcB v u).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
    2
  exact Eventually.of_forall fun p => by
    simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs] using
      covariance_abs_le_two beta B v u p.1.toNNReal p.2

end Problem367.IsingInnovation

end

end OAI
