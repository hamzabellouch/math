import OAI.Probability.PosteriorReplicas.Measures.DensityDifferentiation

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def radialLevel (E : Type*) [NormedAddCommGroup E] (t : ℝ) : Set E :=
  {x | t < Real.exp (-‖x‖^2 / 2)}

def radialWeight (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2)) * volume (radialLevel E t)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E] in
lemma exp_norm_level_ball [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (y : E) {ε : ℝ} (hε : 0 < ε) :
    {x : E | t < Real.exp (-(‖x-y‖ / ε)^2 / 2)} =
      ball y (ε * Real.sqrt (-2 * Real.log t)) := by
  have hlog : Real.log t < 0 := Real.log_neg ht ht1
  have hr : 0 < Real.sqrt (-2 * Real.log t) := Real.sqrt_pos.mpr (by linarith)
  ext x
  simp only [mem_ofPred_eq, mem_ball, dist_eq_norm]
  rw [← Real.log_lt_log_iff ht (Real.exp_pos _), Real.log_exp]
  have hn : 0 ≤ ‖x-y‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hs : (Real.sqrt (-2 * Real.log t))^2 = -2 * Real.log t := Real.sq_sqrt (by linarith)
  constructor
  · intro h
    have : ‖x-y‖ / ε < Real.sqrt (-2 * Real.log t) := by nlinarith
    exact (div_lt_iff₀ hε).mp this |>.trans_eq (mul_comm _ _)
  · intro h
    have : ‖x-y‖ / ε < Real.sqrt (-2 * Real.log t) := (div_lt_iff₀ hε).mpr (by simpa [mul_comm] using h)
    nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E] in
lemma exp_norm_level_empty [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {t : ℝ} (ht : 1 ≤ t) (y : E) (ε : ℝ) :
    {x : E | t < Real.exp (-(‖x-y‖ / ε)^2 / 2)} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he : Real.exp (-(‖x-y‖ / ε)^2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (‖x-y‖ / ε)])
  exact (not_lt_of_ge (he.trans ht)) hx

lemma radialLevel_ball {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    radialLevel E t = ball 0 (Real.sqrt (-2 * Real.log t)) := by
  simpa [radialLevel] using exp_norm_level_ball (E := E) ht ht1 0 (by norm_num : (0:ℝ)<1)

lemma radialLevel_empty {t : ℝ} (ht : 1 ≤ t) : radialLevel E t = ∅ := by
  simpa [radialLevel] using exp_norm_level_empty (E := E) ht 0 1

omit [Nontrivial E] in
@[fun_prop] lemma measurable_radialWeight [Nontrivial E] : Measurable (radialWeight E) := by
  unfold radialWeight radialLevel
  apply Measurable.const_mul
  exact measurable_measure_prodMk_left (show MeasurableSet
    {z : ℝ × E | z.1 < Real.exp (-‖z.2‖^2/2)} from measurableSet_lt (by fun_prop) (by fun_prop))

omit [Nontrivial E] in
lemma lintegral_radialWeight [Nontrivial E] : ∫⁻ t in Ioi (0:ℝ), radialWeight E t = 1 := by
  have hc := lintegral_eq_lintegral_meas_lt (volume : Measure E)
    (f := fun x => Real.exp (-‖x‖^2/2)) (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    (by fun_prop)
  have hg := congrArg (fun μ : Measure E => μ univ) (stdGaussian_density (E := E))
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ] at hg
  have hC : 0 ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  simp only [gaussianRadialDensity, ENNReal.ofReal_mul hC, Measure.restrict_univ,
    ] at hg
  rw [lintegral_const_mul _ (show Measurable (fun x : E => ENNReal.ofReal (Real.exp (-‖x‖^2/2))) by fun_prop)] at hg
  unfold radialWeight radialLevel
  rw [lintegral_const_mul _ (show Measurable (fun t : ℝ =>
    (volume : Measure E) {x | t < Real.exp (-‖x‖^2/2)}) from
    measurable_measure_prodMk_left (show MeasurableSet {z : ℝ × E | z.1 < Real.exp (-‖z.2‖^2/2)} from
      measurableSet_lt (by fun_prop) (by fun_prop))), ← hc]
  exact hg.symm

lemma radialWeight_ne_top {t : ℝ} (ht : 0 < t) : radialWeight E t ≠ ∞ := by
  unfold radialWeight
  by_cases ht1 : t < 1
  · rw [radialLevel_ball ht ht1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  · rw [radialLevel_empty (le_of_not_gt ht1), measure_empty, mul_zero]
    exact ENNReal.zero_ne_top

def scaledRadial (n : ℕ) (y x : E) : ℝ≥0∞ :=
  (ENNReal.ofReal ((noiseScale n) ^ Module.finrank ℝ E))⁻¹ *
    gaussianRadialDensity (Module.finrank ℝ E) (‖x-y‖ / noiseScale n)

lemma scaled_level_ratio {μ : Measure E} (y : E) (n : ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (ENNReal.ofReal ((noiseScale n)^Module.finrank ℝ E))⁻¹ *
      ENNReal.ofReal ((2*Real.pi)^(-(Module.finrank ℝ E:ℝ)/2)) *
      μ {x | t < Real.exp (-(‖x-y‖ / noiseScale n)^2/2)} =
    (μ (ball y (noiseScale n * Real.sqrt (-2*Real.log t))) /
      volume (ball y (noiseScale n * Real.sqrt (-2*Real.log t)))) * radialWeight E t := by
  have hr : 0 < Real.sqrt (-2*Real.log t) := Real.sqrt_pos.mpr (by
    have := Real.log_neg ht ht1
    linarith)
  have hV0 := (measure_ball_pos (volume : Measure E) 0 hr).ne'
  have hVt := (measure_ball_lt_top (μ := (volume : Measure E))
    (x := 0) (r := Real.sqrt (-2*Real.log t))).ne
  rw [exp_norm_level_ball ht ht1 y (noiseScale_pos n), radialWeight, radialLevel_ball ht ht1,
    Measure.addHaar_ball_mul_of_pos volume y (noiseScale_pos n)]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr hVt) (Or.inl ENNReal.ofReal_ne_top)]
  calc
    _ = ((ENNReal.ofReal ((noiseScale n)^Module.finrank ℝ E))⁻¹ *
      ENNReal.ofReal ((2*Real.pi)^(-(Module.finrank ℝ E:ℝ)/2)) *
      μ (ball y (noiseScale n * Real.sqrt (-2*Real.log t)))) *
      (((volume : Measure E) (ball 0 (Real.sqrt (-2*Real.log t))))⁻¹ *
        (volume : Measure E) (ball 0 (Real.sqrt (-2*Real.log t)))) := by
          rw [ENNReal.inv_mul_cancel hV0 hVt, mul_one]
          simp only [div_eq_mul_inv]
    _ = _ := by ring_nf

lemma tendsto_scaledRadial_at_ball_point {μ : Measure E} [IsFiniteMeasure μ]
    {h : E → ℝ≥0∞} (_ : Measurable h) (hμ : μ = volume.withDensity h)
    {M : ℝ≥0∞} (hMt : M ≠ ∞) (hM : ∀ x, h x ≤ M) {y : E}
    (hy : Tendsto (fun r => μ (ball y r) / volume (ball y r)) (𝓝[>] 0) (𝓝 (h y))) :
    Tendsto (fun n => ∫⁻ x, scaledRadial n y x ∂μ) atTop (𝓝 (h y)) := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    (ENNReal.ofReal ((noiseScale n)^Module.finrank ℝ E))⁻¹ *
      ENNReal.ofReal ((2*Real.pi)^(-(Module.finrank ℝ E:ℝ)/2)) *
      μ {x | t < Real.exp (-(‖x-y‖ / noiseScale n)^2/2)}
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    apply Measurable.const_mul
    exact measurable_measure_prodMk_left (show MeasurableSet
      {z : ℝ × E | z.1 < Real.exp (-(‖z.2-y‖ / noiseScale n)^2/2)} from
      measurableSet_lt (by fun_prop) (by fun_prop))
  have hbound : ∀ n, ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), F n t ≤ M * radialWeight E t := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases ht1 : t < 1
    · dsimp only [F]
      rw [scaled_level_ratio y n ht ht1]
      apply mul_le_mul' _ le_rfl
      apply (ENNReal.div_le_iff (measure_ball_pos volume y (mul_pos (noiseScale_pos n)
        (Real.sqrt_pos.mpr (by have := Real.log_neg ht ht1; linarith)))).ne'
        measure_ball_lt_top.ne).mpr
      exact bounded_density_measure_le hμ hM _ measurableSet_ball
    · simp [F, exp_norm_level_empty (le_of_not_gt ht1)]
  have hlim : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      Tendsto (fun n => F n t) atTop (𝓝 (h y * radialWeight E t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    by_cases ht1 : t < 1
    · have hr : 0 < Real.sqrt (-2*Real.log t) := Real.sqrt_pos.mpr (by
        have := Real.log_neg ht ht1; linarith)
      have hε : Tendsto (fun n => noiseScale n * Real.sqrt (-2*Real.log t)) atTop (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        exact ⟨by simpa using tendsto_noiseScale.mul_const (Real.sqrt (-2*Real.log t)),
          Filter.Eventually.of_forall fun n => mul_pos (noiseScale_pos n) hr⟩
      simpa only [F, scaled_level_ratio y _ ht ht1, Function.comp_apply] using
        ENNReal.Tendsto.mul_const (hy.comp hε) (Or.inr (radialWeight_ne_top ht))
    · simp only [F, exp_norm_level_empty (le_of_not_gt ht1), measure_empty, mul_zero,
        radialWeight, radialLevel_empty (le_of_not_gt ht1)]
      exact tendsto_const_nhds
  have H := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Ioi (0:ℝ)))
    (fun t => M * radialWeight E t) hFm hbound
    (by rw [lintegral_const_mul _ measurable_radialWeight, lintegral_radialWeight, mul_one]; exact hMt) hlim
  rw [lintegral_const_mul _ measurable_radialWeight, lintegral_radialWeight, mul_one] at H
  convert H using 1
  funext n
  have hc := lintegral_eq_lintegral_meas_lt μ
    (f := fun x => Real.exp (-(‖x-y‖/noiseScale n)^2/2))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) (by fun_prop)
  have hC : 0 ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  simp only [scaledRadial, gaussianRadialDensity, ENNReal.ofReal_mul hC, ← mul_assoc]
  rw [lintegral_const_mul _ (by fun_prop), hc]
  symm
  exact lintegral_const_mul _ (measurable_measure_prodMk_left (show MeasurableSet
    {z : ℝ × E | z.1 < Real.exp (-(‖z.2-y‖ / noiseScale n)^2/2)} from
    measurableSet_lt (by fun_prop) (by fun_prop)))

end Generic
end PosteriorReplicas
end

end OAI
