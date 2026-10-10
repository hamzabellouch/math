import OAI.Analysis.IrrationalRotation.Model.TrialSampling
import OAI.Analysis.IrrationalRotation.Sampling.NonresonantPhaseTrials
import OAI.Analysis.IrrationalRotation.Analysis.FiniteTestSelection
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingLp

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.TrialSampling

instance spatialLaw_probability (m : ℕ) : IsProbabilityMeasure (spatialLaw m) := by
  let : IsProbabilityMeasure circleMeasure := ⟨by
    simp [circleMeasure, AddCircle.measure_univ]⟩
  dsimp [spatialLaw]
  infer_instance

lemma phaseLaw_probability (m : ℕ) {N : ℝ} (hN : 0 < N) :
    IsProbabilityMeasure (phaseLaw m N) := by
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  dsimp [phaseLaw]
  infer_instance

lemma phaseLaw_eq_pi (m : ℕ) {N : ℝ} (hN : 0 < N) :
    phaseLaw m N = Measure.pi (fun _ : Fin m =>
      ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) := by
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  exact Measure.infinitePi_eq_pi _

lemma measurable_kernel_pair (m : ℕ) :
    Measurable (fun p : ℝ × ℝ => CircleParameterData.kernel m p.1 p.2) := by
  have hd : Measurable (fun p : ℝ × ℝ => CircleParameterData.delta p.1) :=
    measurable_fst.fract.min (measurable_const.sub measurable_fst.fract)
  unfold CircleParameterData.kernel
  apply Measurable.ite
  · exact (measurableSet_le measurable_const hd).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.mul hd)))
  · exact measurable_const.div (measurable_const.mul hd)
  · exact measurable_const

lemma measurable_orientedKernel_pair (m : ℕ) (endpoint : Bool) :
    Measurable (fun p : ℝ × ℝ =>
      CircleParameterData.orientedKernel endpoint m p.1 p.2) := by
  cases endpoint
  · exact measurable_kernel_pair m
  · exact (measurable_kernel_pair m).comp
      ((measurable_fst.sub measurable_snd).prodMk measurable_snd)

lemma measurable_average_pair (m : ℕ) (samples : Finset ℕ) (endpoint : Bool) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      average m samples endpoint p.1 p.2) := by
  unfold average
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro n hn
  apply Finset.measurable_prod
  intro i hi
  have hz : Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      CircleParameterData.rep (p.2 i)) :=
    CircleParameterData.measurable_rep.comp
      ((show Measurable (fun z : Fin m → Circle => z i) from measurable_pi_apply i).comp
        measurable_snd)
  have hv : Measurable (fun p : (Fin m → ℝ) × (Fin m → Circle) =>
      Int.fract ((n : ℝ) * p.1 i)) :=
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).fract
  exact (measurable_orientedKernel_pair m endpoint).comp (hz.prodMk hv)

lemma measurable_squaredError (m : ℕ) (samples : Finset ℕ) (endpoint : Bool) :
    Measurable (squaredError m samples endpoint) := by
  exact (((measurable_average_pair m samples endpoint).sub_const 1).pow_const 2).ennreal_ofReal.lintegral_prod_right'

lemma squaredError_eq_eLpNorm_sq (m : ℕ) (samples : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) :
    squaredError m samples endpoint phase =
      eLpNorm (fun z => average m samples endpoint phase z - 1) 2 (spatialLaw m) ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := fun z => average m samples endpoint phase z - 1)
    (μ := spatialLaw m) (p := (2 : NNReal)) (by norm_num)
    (((measurable_average_pair m samples endpoint).comp
      (measurable_const.prodMk measurable_id)).sub_const 1).aestronglyMeasurable
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [h]
  apply lintegral_congr
  intro z
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

lemma squaredError_lt_iff_eLpNorm_lt (m : ℕ) (samples : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    squaredError m samples endpoint phase < ENNReal.ofReal (r ^ 2) ↔
      eLpNorm (fun z => average m samples endpoint phase z - 1) 2 (spatialLaw m) <
        ENNReal.ofReal r := by
  rw [squaredError_eq_eLpNorm_sq, ENNReal.ofReal_pow hr]
  simpa only [ENNReal.rpow_two] using
    (ENNReal.rpow_lt_rpow_iff (x := eLpNorm (fun z => average m samples endpoint phase z - 1)
      2 (spatialLaw m)) (y := ENNReal.ofReal r) (z := (2 : ℝ)) (by norm_num))

theorem exists_strict_trials_of_moment_budget
    (m : ℕ) {N : ℝ} (hN : 0 < N) (hm : 100 ≤ (m : ℝ))
    {ι : Type*} (s : Finset ι) (samples : ι → Finset ℕ)
    {ε δ : ℝ≥0∞} (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hmoment : ∀ t ∈ s, ∀ endpoint : Bool,
      (∫⁻ phase, squaredError m (samples t) endpoint phase ∂phaseLaw m N) ≤ δ)
    (hbudget : ENNReal.ofReal (ProductPhases.failureBound m) +
      (2 * s.card : ℝ≥0∞) * (δ / ε) < 1) :
    ∃ phase : Fin m → ℝ,
      (∀ i, phase i ∈ Set.Ioo (1 / N) (2 / N)) ∧
      (∀ i, ∀ k : ℤ, k ≠ 0 → Int.fract ((k : ℝ) * phase i) ≠ 0) ∧
      ProductPhases.strictLargePhaseCondition Finset.univ N phase ∧
      ∀ t ∈ s, ∀ endpoint : Bool, squaredError m (samples t) endpoint phase < ε := by
  classical
  let ν : Fin m → Measure ℝ := fun _ =>
    ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))
  let : IsProbabilityMeasure
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) hN)
  let : NullSingletonClass
      (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))) :=
    InvariantProjection.IndependentAngles.intervalLaw_nullSingletonClass _ _
  let : IsProbabilityMeasure (phaseLaw m N) := phaseLaw_probability m hN
  have hbad : phaseLaw m N
      (ProductPhases.strictLargePhaseFailure (Finset.univ : Finset (Fin m)) N) ≤
      ENNReal.ofReal (ProductPhases.failureBound m) := by
    simpa only [phaseLaw, Finset.card_univ, Fintype.card_fin] using
      ProductPhases.uniformProduct_measure_strictLargePhaseFailure_le
        (fun _ : Fin m => N) (fun _ => hN) Finset.univ hN
        (by simpa only [Finset.card_univ, Fintype.card_fin] using hm) (fun _ _ => rfl)
  have hP := (ProductPhases.intervalProduct_ae_strict_bounds
      (fun _ : Fin m => N) (fun _ => hN)).and
    (ProductPhases.infinitePi_ae_nonresonant ν)
  obtain ⟨phase, hphase, hspread, htests⟩ :=
    Invariant233.exists_finite_tests_of_uniform_expectation_bound
      (phaseLaw m N) (s.product (Finset.univ : Finset Bool))
      (fun t => squaredError m (samples t.1) t.2)
      (ProductPhases.strictLargePhaseFailure Finset.univ N) hε0 hεtop
      (fun t _ => (measurable_squaredError m (samples t.1) t.2).aemeasurable)
      (fun t ht => hmoment t.1 (Finset.mem_product.mp ht).1 t.2)
      hbad (by simpa [Finset.card_product, mul_comm] using hbudget)
      _ hP
  refine ⟨phase, hphase.1, hphase.2,
    (ProductPhases.not_mem_strictLargePhaseFailure_iff Finset.univ hN phase).mp hspread, ?_⟩
  intro t ht endpoint
  exact htests (t, endpoint) (Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩)

lemma tendsto_failureBound_nat :
    Tendsto (fun m : ℕ => ENNReal.ofReal (ProductPhases.failureBound m)) atTop (𝓝 0) := by
  have hs := ProductPhases.summable_failureBound_of_nat_le
    (m := fun n : ℕ => (n : ℝ)) (fun _ => le_rfl) (fun n => Nat.cast_nonneg n)
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hs.tendsto_atTop_zero

theorem eventually_exists_strict_trials_of_moments_tendsto_zero
    {ι : Type*} (s : Finset ι) (N : ℕ → ℝ) (hN : ∀ᶠ m in atTop, 0 < N m)
    (samples : ℕ → ι → Finset ℕ)
    {ε : ℝ≥0∞} (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞)
    (hmoment : ∀ t ∈ s, ∀ endpoint : Bool,
      Tendsto (fun m => ∫⁻ phase, squaredError m (samples m t) endpoint phase
        ∂phaseLaw m (N m)) atTop (𝓝 0)) :
    ∀ᶠ m in atTop, ∃ phase : Fin m → ℝ,
      (∀ i, phase i ∈ Set.Ioo (1 / N m) (2 / N m)) ∧
      (∀ i, ∀ k : ℤ, k ≠ 0 → Int.fract ((k : ℝ) * phase i) ≠ 0) ∧
      ProductPhases.strictLargePhaseCondition Finset.univ (N m) phase ∧
      ∀ t ∈ s, ∀ endpoint : Bool, squaredError m (samples m t) endpoint phase < ε := by
  classical
  let tests := s.product (Finset.univ : Finset Bool)
  let δ : ℕ → ℝ≥0∞ := fun m => ∑ t ∈ tests,
    ∫⁻ phase, squaredError m (samples m t.1) t.2 phase ∂phaseLaw m (N m)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h := tendsto_finsetSum tests (fun t ht =>
      hmoment t.1 (Finset.mem_product.mp ht).1 t.2)
    simpa only [Finset.sum_const_zero] using h
  have hdiv : Tendsto (fun m => δ m / ε) atTop (𝓝 0) := by
    simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hδ (Or.inr hε0)
  have hmul : Tendsto (fun m => (2 * s.card : ℝ≥0∞) * (δ m / ε)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := (2 * s.card : ℝ≥0∞)) hdiv
        (Or.inr (by finiteness)))
  have hbudget : ∀ᶠ (m : ℕ) in atTop,
      ENNReal.ofReal (ProductPhases.failureBound m) +
        (2 * s.card : ℝ≥0∞) * (δ m / ε) < 1 := by
    have hlim := tendsto_failureBound_nat.add hmul
    have h := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) + 0 < 1))
    exact h
  filter_upwards [hN, eventually_ge_atTop (100 : ℕ), hbudget] with m hmN hm hmbudget
  apply exists_strict_trials_of_moment_budget m hmN (by exact_mod_cast hm)
    s (samples m) hε0 hεtop _ hmbudget
  intro t ht endpoint
  exact Finset.single_le_sum (s := tests) (a := (t, endpoint))
    (f := fun u : ι × Bool => ∫⁻ phase, squaredError m (samples m u.1) u.2 phase
      ∂phaseLaw m (N m)) (fun _ _ => zero_le)
    (Finset.mem_product.mpr ⟨ht, Finset.mem_univ endpoint⟩)

theorem exists_strict_trials_with_source_L2_bound
    (m j : ℕ) (hj : 0 < j) {N : ℝ} (hN : 0 < N) (hm : 100 ≤ (m : ℝ))
    {ι : Type*} (s : Finset ι) (samples : ι → Finset ℕ)
    {δ : ℝ≥0∞}
    (hmoment : ∀ t ∈ s, ∀ endpoint : Bool,
      (∫⁻ phase, squaredError m (samples t) endpoint phase ∂phaseLaw m N) ≤ δ)
    (hbudget : ENNReal.ofReal (ProductPhases.failureBound m) +
      (2 * s.card : ℝ≥0∞) * (δ / ENNReal.ofReal ((1 / (2 * (j : ℝ))) ^ 2)) < 1) :
    ∃ phase : Fin m → ℝ,
      (∀ i, phase i ∈ Set.Ioo (1 / N) (2 / N)) ∧
      (∀ i, ∀ k : ℤ, k ≠ 0 → Int.fract ((k : ℝ) * phase i) ≠ 0) ∧
      ProductPhases.strictLargePhaseCondition Finset.univ N phase ∧
      ∀ t ∈ s, ∀ endpoint : Bool,
        eLpNorm (fun z => average m (samples t) endpoint phase z - 1) 2 (spatialLaw m) <
          ENNReal.ofReal (1 / (2 * (j : ℝ))) := by
  have hr : 0 < 1 / (2 * (j : ℝ)) := by positivity
  obtain ⟨phase, hbox, hnonres, hspread, htests⟩ :=
    exists_strict_trials_of_moment_budget m hN hm s samples
      (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)))
      ENNReal.ofReal_ne_top hmoment hbudget
  refine ⟨phase, hbox, hnonres, hspread, ?_⟩
  intro t ht endpoint
  exact (squaredError_lt_iff_eLpNorm_lt m (samples t) endpoint phase hr.le).mp
    (htests t ht endpoint)

end Invariant233.TrialSampling

end

end OAI
