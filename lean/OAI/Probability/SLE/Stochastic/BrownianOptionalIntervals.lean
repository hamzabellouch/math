import OAI.Probability.SLE.Stochastic.BrownianOptionalInequality

namespace OAI

/-! Conditional optional stopping between two bounded stopping times.
The compensated identity follows from the discrete grid identity. The drift is required to have its sign only between the two
stops, as needed between multipoint activation and completion switches. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma SmoothTimeBrownianField.eval_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0}
    {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) :
    Measurable (fun q : ℝ≥0 × Ω => F q.1 q.2 (B q.1 q.2)) := by
  convert (hF.joint 0 (by decide)).comp (measurable_id.prodMk hBm) using 1
  funext q
  simp only [iteratedDeriv_zero, Function.comp_apply, id_eq]

lemma SmoothTimeBrownianField.compensated_joint_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0}
    {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) :
    Measurable (fun q : ℝ≥0 × Ω => brownianFieldCompensated B F a q.1 q.2) :=
  (hF.eval_joint_measurable hBm).sub
    (cumulative_integral_measurable _ (hF.generator_measurable hBm))

lemma SmoothTimeBrownianField.compensated_bound
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0}
    {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (T t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    |brownianFieldCompensated B F a t ω| ≤ (K : ℝ) + 2 * K * T := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (C := 2 * (K : ℝ))
    (f := fun u => brownianFieldDrift B F a u ω)
    (fun u _ => by simpa only [Real.norm_eq_abs] using hF.generator_bound u ω)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.coe_nonneg] at hi
  exact (abs_sub _ _).trans (add_le_add (hF.bound t ω (B t ω) 0 (by decide))
    (hi.trans (mul_le_mul_of_nonneg_left ht (by positivity))))

lemma SmoothTimeBrownianField.compensated_path_continuous
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    {hm : ∀ t, Measurable (B t)} {K : ℝ≥0}
    {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t => brownianFieldCompensated B F a t ω) := by
  have hi (s t : ℝ) : IntervalIntegrable (fun u => brownianFieldDrift B F a u ω)
      volume s t := by
    rcases le_total s t with h | h
    · exact bounded_time_section_intervalIntegrable s t h _ (hF.generator_measurable hBm)
        (2 * (K : ℝ)) hF.generator_bound ω
    · exact (bounded_time_section_intervalIntegrable t s h _ (hF.generator_measurable hBm)
        (2 * (K : ℝ)) hF.generator_bound ω).symm
  exact (hF.path_continuous hBc ω).sub
    ((intervalIntegral.continuous_primitive hi 0).comp continuous_subtype_val)

lemma SmoothTimeBrownianField.eval_stopped_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)} {K : ℝ≥0}
    {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {τ : Ω → ℝ≥0} (hτm : Measurable τ) :
    Integrable (fun ω => F (τ ω) ω (B (τ ω) ω)) P := by
  apply Integrable.of_bound
    ((hF.eval_joint_measurable hBm).comp (hτm.prodMk measurable_id)).aestronglyMeasurable
    (K : ℝ)
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq, iteratedDeriv_zero] using
      hF.bound (τ ω) ω (B (τ ω) ω) 0 (by decide)

lemma SmoothTimeBrownianField.compensated_stopped_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)} {K : ℝ≥0}
    {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    {τ : Ω → ℝ≥0} (hτm : Measurable τ) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => brownianFieldCompensated B F a (τ ω) ω) P := by
  apply Integrable.of_bound
    ((hF.compensated_joint_measurable hBm).comp (hτm.prodMk measurable_id)).aestronglyMeasurable
    ((K : ℝ) + 2 * K * T)
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using
      hF.compensated_bound T (τ ω) (hb ω) ω

/-- The full compensated optional identity. No sign restriction on the
drift is needed for this identity. -/
theorem brownian_compensated_optional_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T) :
    (∫ ω, brownianFieldCompensated B F a (τ ω) ω ∂P) =
      ∫ ω, F 0 ω (B 0 ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hτm := stopping_time_measurable_nnreal hτ
  have hCm := hF.compensated_joint_measurable hBm
  let V (n : ℕ) (ω : Ω) := brownianFieldCompensated B F a (stopGrid n (τ ω)) ω
  have hVm (n : ℕ) : Measurable (V n) :=
    measurable_discrete_eval (fun k ω => brownianFieldCompensated B F a (stopGridTime n k) ω)
      (fun k => hCm.comp measurable_prodMk_left) (stopGridIndex_measurable hτm n)
  have hVb (n : ℕ) (ω : Ω) : |V n ω| ≤ (K : ℝ) + 2 * K * (T + 1) := by
    apply hF.compensated_bound (T + 1) _ _ ω
    have hgrid := (stopGrid_bounds n (τ ω)).2
    have hone : (1 : ℝ≥0) / ((n : ℝ≥0) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      simp
    exact hgrid.trans (add_le_add (hb ω) hone)
  have hlim : Tendsto (fun n => ∫ ω, V n ω ∂P) atTop
      (𝓝 (∫ ω, brownianFieldCompensated B F a (τ ω) ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => (K : ℝ) + 2 * K * (T + 1))
      (fun n => (hVm n).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
    exact ae_of_all _ fun ω =>
      (hF.compensated_path_continuous hBm hBc ω).continuousAt.tendsto.comp
        (stopGrid_tendsto (τ ω))
  have he (n : ℕ) : (∫ ω, V n ω ∂P) = ∫ ω, F 0 ω (B 0 ω) ∂P :=
    brownian_compensated_grid_integral hB hm hBm hF τ hτ T hb n
  have hlim' : Tendsto (fun n => ∫ ω, V n ω ∂P) atTop
      (𝓝 (∫ ω, F 0 ω (B 0 ω) ∂P)) := by
    have heq : (fun n => ∫ ω, V n ω ∂P) = fun _ : ℕ => ∫ ω, F 0 ω (B 0 ω) ∂P :=
      funext he
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hlim'

lemma stopping_time_piecewise_after
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) {A : Set Ω} [DecidablePred (· ∈ A)]
    (hA : MeasurableSet[hσ.measurableSpace] A) :
    IsStoppingTime ℱ (fun ω => ((if ω ∈ A then τ ω else σ ω) : WithTop ℝ≥0)) := by
  classical
  intro t
  have hAt := (hσ.measurableSet A).mp hA |>.2 t
  have hAct := (hσ.measurableSet Aᶜ).mp hA.compl |>.2 t
  convert (hAt.inter (hτ t)).union hAct using 1
  ext ω
  by_cases hω : ω ∈ A
  · simp only [hω, ite_true, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff,
      not_true_eq_false, false_and, or_false, true_and, WithTop.coe_le_coe]
    exact ⟨fun h => ⟨(hστ ω).trans h, h⟩, fun h => h.2⟩
  · simp [hω]

/-- Conditional compensated equality between two bounded stopping times. -/
theorem brownian_compensated_optional_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    (∫ ω in A, brownianFieldCompensated B F a (τ ω) ω -
      brownianFieldCompensated B F a (σ ω) ω ∂P) = 0 := by
  classical
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let π := fun ω => if ω ∈ A then τ ω else σ ω
  have hπ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (π ω : WithTop ℝ≥0)) := by
    convert stopping_time_piecewise_after _ hσ hτ hστ hA using 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [π, hω] <;> rfl
  have hbσ : ∀ ω, σ ω ≤ T := fun ω => (hστ ω).trans (hb ω)
  have hbπ : ∀ ω, π ω ≤ T := by
    intro ω
    dsimp only [π]
    split_ifs
    · exact hb ω
    · exact hbσ ω
  have hπi := hF.compensated_stopped_integrable hBm (stopping_time_measurable_nnreal hπ) T hbπ
    (P := P)
  have hσi := hF.compensated_stopped_integrable hBm (stopping_time_measurable_nnreal hσ) T hbσ
    (P := P)
  have heπ := brownian_compensated_optional_integral hB hm hBm hBc hF π hπ T hbπ
  have heσ := brownian_compensated_optional_integral hB hm hBm hBc hF σ hσ T hbσ
  have hpoint (ω : Ω) : brownianFieldCompensated B F a (π ω) ω -
      brownianFieldCompensated B F a (σ ω) ω =
      A.indicator (fun ω => brownianFieldCompensated B F a (τ ω) ω -
        brownianFieldCompensated B F a (σ ω) ω) ω := by
    by_cases hω : ω ∈ A <;> simp [π, hω]
  have he : (∫ ω, brownianFieldCompensated B F a (π ω) ω -
      brownianFieldCompensated B F a (σ ω) ω ∂P) = 0 := by
    rw [integral_sub hπi hσi, heπ, heσ, sub_self]
  simpa only [hpoint, integral_indicator (hσ.measurableSpace_le _ hA)] using he

/-- Only the drift between the stops needs to be nonpositive, and the
inequality remains valid after restricting to any event known at the
first stop. -/
theorem brownian_time_field_optional_interval_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {K : ℝ≥0} {F a : ℝ≥0 → Ω → ℝ → ℝ}
    (hF : SmoothTimeBrownianField B hm K F a)
    (σ τ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A)
    (hnonpos : ∀ ω ∈ A, ∀ u, (σ ω : ℝ) ≤ u → u < (τ ω : ℝ) →
      brownianFieldDrift B F a u ω ≤ 0) :
    (∫ ω in A, F (τ ω) ω (B (τ ω) ω) ∂P) ≤
      ∫ ω in A, F (σ ω) ω (B (σ ω) ω) ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbσ : ∀ ω, σ ω ≤ T := fun ω => (hστ ω).trans (hb ω)
  have hσm := stopping_time_measurable_nnreal hσ
  have hτm := stopping_time_measurable_nnreal hτ
  have hFσ := hF.eval_stopped_integrable hBm hσm (P := P.restrict A)
  have hFτ := hF.eval_stopped_integrable hBm hτm (P := P.restrict A)
  have hCσ := hF.compensated_stopped_integrable hBm hσm T hbσ (P := P.restrict A)
  have hCτ := hF.compensated_stopped_integrable hBm hτm T hb (P := P.restrict A)
  have hCm := brownian_compensated_optional_interval hB hm hBm hBc hF σ τ hσ hτ hστ T hb hA
  have hGm := hF.generator_measurable hBm
  have hi (s t : ℝ) (hst : s ≤ t) (ω : Ω) :=
    bounded_time_section_intervalIntegrable s t hst _ hGm (2 * (K : ℝ)) hF.generator_bound ω
  have hle : (∫ ω in A, F (τ ω) ω (B (τ ω) ω) - F (σ ω) ω (B (σ ω) ω) ∂P) ≤
      ∫ ω in A, brownianFieldCompensated B F a (τ ω) ω -
        brownianFieldCompensated B F a (σ ω) ω ∂P := by
    apply integral_mono_ae (hFτ.sub hFσ) (hCτ.sub hCσ)
    filter_upwards [ae_restrict_mem (hσ.measurableSpace_le _ hA)] with ω hω
    have hστreal : (σ ω : ℝ) ≤ (τ ω : ℝ) := hστ ω
    have hneg : (∫ u in (σ ω : ℝ)..(τ ω : ℝ), brownianFieldDrift B F a u ω) ≤ 0 := by
      have hh := intervalIntegral.integral_mono_on_of_le_Ioo hστreal
        (hi (σ ω) (τ ω) hστreal ω) (intervalIntegrable_const (c := (0 : ℝ)))
        (fun u hu => hnonpos ω hω u hu.1.le hu.2)
      simpa only [intervalIntegral.integral_zero] using hh
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 (σ ω) (σ ω).coe_nonneg ω) (hi (σ ω) (τ ω) (hστ ω) ω)
    dsimp only [brownianFieldCompensated, Pi.sub_apply]
    linarith
  rw [hCm, integral_sub hFτ hFσ] at hle
  exact sub_nonpos.mp hle

end SLEExactGauge

end

end OAI
