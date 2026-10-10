import OAI.Probability.SLE.OptionalStopping

namespace OAI

/-! A one-sided optional-stopping estimate for the discounted multipoint
product, obtained from the centered grid identity and the sign of the drift. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma bounded_cumulative_at_grid_le
    {Ω : Type*} [MeasurableSpace Ω] (G : ℝ → Ω → ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ u ω, |G u ω| ≤ C) (τ : Ω → ℝ≥0)
    (hnonpos : ∀ ω u, 0 ≤ u → u < (τ ω : ℝ) → G u ω ≤ 0)
    (n : ℕ) (ω : Ω) :
    (∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), G u ω) ≤
      C*(1/((n : ℝ)+1)) := by
  have hi₀ := bounded_time_section_intervalIntegrable 0 (τ ω) (τ ω).coe_nonneg G hG C hb ω
  have h0 : (∫ u in (0 : ℝ)..(τ ω : ℝ), G u ω) ≤ 0 := by
    have hh := intervalIntegral.integral_mono_on_of_le_Ioo (τ ω).coe_nonneg hi₀
      (intervalIntegrable_const (c := (0 : ℝ)))
      (fun u hu => hnonpos ω u hu.1.le hu.2)
    simpa only [intervalIntegral.integral_zero] using hh
  have hle : (τ ω : ℝ) ≤ stopGrid n (τ ω) := (stopGrid_bounds n (τ ω)).1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi₀
    (bounded_time_section_intervalIntegrable (τ ω) (stopGrid n (τ ω)) hle G hG C hb ω)
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (τ ω : ℝ)) (b := (stopGrid n (τ ω) : ℝ)) (C := C)
    (f := fun u => G u ω) (fun u _ => by simpa only [Real.norm_eq_abs] using hb u ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)] at hbnd
  have hupper := (stopGrid_bounds n (τ ω)).2
  have hu : (stopGrid n (τ ω) : ℝ) ≤ (τ ω : ℝ)+1/((n : ℝ)+1) := by exact_mod_cast hupper
  have htail := (le_abs_self _).trans hbnd
  have hrange := mul_le_mul_of_nonneg_left (show (stopGrid n (τ ω) : ℝ)-(τ ω : ℝ) ≤
    1/((n : ℝ)+1) by linarith) hC
  linarith

theorem brownian_time_field_optional_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (K : ℝ≥0) (F a : ℝ≥0 → Ω → ℝ → ℝ)
    (hF : SmoothTimeBrownianField B hm K F a)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B
      (fun t => (hm t).stronglyMeasurable)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ ω, τ ω ≤ T)
    (hnonpos : ∀ ω u, 0 ≤ u → u < (τ ω : ℝ) → brownianFieldDrift B F a u ω ≤ 0) :
    (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P) ≤ (∫ ω, F 0 ω (B 0 ω) ∂P) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hτm := stopping_time_measurable_nnreal hτ
  let V (n : ℕ) (ω : Ω) := F (stopGrid n (τ ω)) ω (B (stopGrid n (τ ω)) ω)
  let H (n : ℕ) (ω : Ω) := ∫ u in (0 : ℝ)..(stopGrid n (τ ω) : ℝ), brownianFieldDrift B F a u ω
  have hVm (n : ℕ) : Measurable (V n) :=
    measurable_discrete_eval (fun k ω => F (stopGridTime n k) ω (B (stopGridTime n k) ω))
      (fun k => hF.eval_measurable _ 0 (by decide) (hm _)) (stopGridIndex_measurable hτm n)
  have hVb (n : ℕ) (ω : Ω) : |V n ω| ≤ (K : ℝ) := hF.bound _ ω _ 0 (by decide)
  have hVi (n : ℕ) : Integrable (V n) P :=
    Integrable.of_bound (hVm n).aestronglyMeasurable (K : ℝ)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
  have hGm := hF.generator_measurable hBm
  have hHjoint := cumulative_integral_measurable _ hGm
  have hHm (n : ℕ) : Measurable (H n) :=
    measurable_discrete_eval
      (fun k ω => ∫ u in (0 : ℝ)..(stopGridTime n k : ℝ), brownianFieldDrift B F a u ω)
      (fun k => hHjoint.comp measurable_prodMk_left) (stopGridIndex_measurable hτm n)
  have hHb (n : ℕ) (ω : Ω) : |H n ω| ≤ 2*(K : ℝ)*((T : ℝ)+1) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (stopGrid n (τ ω) : ℝ)) (C := 2*(K : ℝ))
      (f := fun u => brownianFieldDrift B F a u ω)
      (fun u _ => by simpa only [Real.norm_eq_abs] using hF.generator_bound u ω)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (stopGrid n (τ ω)).coe_nonneg] at hbound
    have hupper := (stopGrid_bounds n (τ ω)).2
    have hgrid : (stopGrid n (τ ω) : ℝ) ≤ (τ ω : ℝ)+1/((n : ℝ)+1) := by exact_mod_cast hupper
    have hT : (τ ω : ℝ) ≤ T := hb ω
    have hone : 1/((n : ℝ)+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact hbound.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hHi (n : ℕ) : Integrable (H n) P :=
    Integrable.of_bound (hHm n).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hHb n ω)
  have hHle (n : ℕ) (ω : Ω) : H n ω ≤ 2*(K : ℝ)*(1/((n : ℝ)+1)) :=
    bounded_cumulative_at_grid_le _ hGm (2*(K : ℝ)) (by positivity)
      hF.generator_bound τ hnonpos n ω
  have hmean (n : ℕ) : (∫ ω, V n ω ∂P) ≤
      (∫ ω, F 0 ω (B 0 ω) ∂P)+2*(K : ℝ)*(1/((n : ℝ)+1)) := by
    have he := brownian_compensated_grid_integral hB hm hBm hF τ hτ T hb n
    change (∫ ω, V n ω-H n ω ∂P) = _ at he
    rw [integral_sub (hVi n) (hHi n)] at he
    have hi := integral_mono_ae (hHi n) (integrable_const (2*(K : ℝ)*(1/((n : ℝ)+1))))
      (Eventually.of_forall (hHle n))
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
    linarith
  have hlim : Tendsto (fun n => ∫ ω, V n ω ∂P) atTop
      (𝓝 (∫ ω, F (τ ω) ω (B (τ ω) ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (K : ℝ))
      (fun n => (hVm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hVb n ω)
    exact Eventually.of_forall fun ω =>
      (hF.path_continuous hBc ω).continuousAt.tendsto.comp (stopGrid_tendsto (τ ω))
  have hlimUpper : Tendsto (fun n : ℕ => (∫ ω, F 0 ω (B 0 ω) ∂P)+
      2*(K : ℝ)*(1/((n : ℝ)+1))) atTop (𝓝 (∫ ω, F 0 ω (B 0 ω) ∂P)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*(K : ℝ)))
  exact le_of_tendsto_of_tendsto hlim hlimUpper (Eventually.of_forall hmean)

end SLEExactGauge

end

end OAI
