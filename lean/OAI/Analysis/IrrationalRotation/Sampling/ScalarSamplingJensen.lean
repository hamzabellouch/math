import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingShear

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

lemma sq_integral_le_integral_sq_unit {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1)
    (hfsq : IntervalIntegrable (fun x => f x ^ 2) volume 0 1) :
    (∫ x in (0 : ℝ)..1, f x)^2 ≤ ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  let c : ℝ := ∫ x in (0 : ℝ)..1, f x
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1, (f x - c)^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)
  have heq : (fun x => (f x - c)^2) = fun x => (f x^2 - (2*c)*f x) + c^2 := by
    funext x; ring
  rw [heq, intervalIntegral.integral_add (hfsq.sub (hf.const_mul (2*c)))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c^2) volume 0 1),
    intervalIntegral.integral_sub hfsq (hf.const_mul (2*c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [sub_zero, one_smul] at hn
  change c^2 ≤ ∫ x in (0 : ℝ)..1, f x^2
  change 0 ≤ (∫ x in (0 : ℝ)..1, f x^2) - (2*c)*c + c^2 at hn
  nlinarith

lemma intervalIntegrable_unit_of_measurable_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ C) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  apply IntegrableOn.of_bound (by simp) hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall hb

lemma measurable_interval_average {F : ℝ → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => ∫ y in (0 : ℝ)..1, F x y) := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact hF.stronglyMeasurable.integral_prod_right.measurable

lemma endpoint_average_integrable {h α : ℝ} (hh : 0 < h) (hα : 0 < α) :
    IntervalIntegrable (fun z => ∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v) volume 0 1 ∧
    IntervalIntegrable (fun z => (∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v)^2) volume 0 1 := by
  have hm : Measurable (fun p : ℝ × ℝ => circleKernel h α (p.1-p.2) p.2) :=
    (measurable_circleKernel h α).comp ((measurable_fst.sub measurable_snd).prodMk measurable_snd)
  have hbar := measurable_interval_average (F := fun z v => circleKernel h α (z-v) v) hm
  have hb (z : ℝ) : ‖∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v‖ ≤ (h*α)⁻¹ := by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const
      (fun v (_ : v ∈ uIoc (0 : ℝ) 1) => circleKernel_norm_le hh hα (z-v) v)
  constructor
  · exact intervalIntegrable_unit_of_measurable_bound hbar hb
  · apply intervalIntegrable_unit_of_measurable_bound (hbar.pow_const 2)
    intro z
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb z) 2

theorem circleEndpoint_averaged_secondMoment_lower {h α : ℝ} (hh : 0 < h)
    (hhone : h ≤ 1) (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (1 - 2*α)^2 ≤ ∫ z in (0 : ℝ)..1,
      (∫ v in (0 : ℝ)..1, circleKernel h α (z-v) v)^2 := by
  obtain ⟨hi, hisq⟩ := endpoint_average_integrable hh hα
  have hj := sq_integral_le_integral_sq_unit hi hisq
  rwa [endpoint_circleKernel_mass hh hhone hα hαhalf] at hj

theorem manuscriptEndpointKernel_averaged_secondMoment_lower_from_mass {m : ℕ} (hm : 200 ≤ m) :
    (1 - 2 / (m : ℝ)^2)^2 ≤ ∫ z in (0 : ℝ)..1,
      (∫ v in (0 : ℝ)..1, manuscriptEndpointKernel m z v)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptEndpointKernel, manuscriptKernel, mul_one_div] using
    circleEndpoint_averaged_secondMoment_lower hh hhone hα hαhalf

end Invariant233.ScalarSampling

end OAI
