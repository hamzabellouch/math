import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem336AdditiveD139.NoisePast

variable {S : Type u_1} {N : Type u_2} {E : Type u_3} {H : Type u_4} {O : Type u_5}
  [MeasurableSpace S] [MeasurableSpace N] [MeasurableSpace E]
  [MeasurableSpace H] [MeasurableSpace O]
  {μ : Measure S} {P : Measure N}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure P]

theorem indepFun_snd_signal_history {Q : N → E} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) :
    IndepFun (fun ω : S × N => Q ω.2)
      (fun ω : S × N => (ω.1, hist ω.2)) (μ.prod P) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A C hA hC
  have hQA : MeasurableSet ((fun ω : S × N => Q ω.2) ⁻¹' A) :=
    hA.preimage (hQ.comp measurable_snd)
  have hHC : MeasurableSet ((fun ω : S × N => (ω.1, hist ω.2)) ⁻¹' C) :=
    hC.preimage (measurable_fst.prodMk (hhist.comp measurable_snd))
  rw [Measure.prod_apply (hQA.inter hHC), Measure.prod_apply hQA,
    Measure.prod_apply hHC]
  have hsec (x : S) : MeasurableSet (Prod.mk x ⁻¹' C) :=
    hC.preimage (measurable_const.prodMk measurable_id)
  have heq (x : S) :
      P (Prod.mk x ⁻¹' (((fun ω : S × N => Q ω.2) ⁻¹' A) ∩
        ((fun ω : S × N => (ω.1, hist ω.2)) ⁻¹' C))) =
        P (Q ⁻¹' A) * P (hist ⁻¹' (Prod.mk x ⁻¹' C)) := by
    exact hind.measure_inter_preimage_eq_mul A (Prod.mk x ⁻¹' C) hA (hsec x)
  simp_rw [heq]
  simp only [Set.preimage_preimage]
  change (∫⁻ x, P (Q ⁻¹' A) * P (hist ⁻¹' (Prod.mk x ⁻¹' C)) ∂μ) =
    (∫⁻ _ : S, P (Q ⁻¹' A) ∂μ) *
      ∫⁻ x, P (hist ⁻¹' (Prod.mk x ⁻¹' C)) ∂μ
  rw [lintegral_const_mul' _ _ (measure_ne_top _ _)]
  simp

theorem indepFun_snd_observation {Q : N → E} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) (observe : S × H → O)
    (hobserve : Measurable observe) :
    IndepFun (fun ω : S × N => Q ω.2)
      (fun ω : S × N => observe (ω.1, hist ω.2)) (μ.prod P) := by
  exact (indepFun_snd_signal_history (μ := μ) hQ hhist hind).comp
    measurable_id hobserve

theorem condExp_snd_observation {Q : N → E} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) (observe : S × H → O)
    (hobserve : Measurable observe) (f : E → ℝ) (hf : Measurable f) :
    (μ.prod P)[(fun ω : S × N => f (Q ω.2)) |
      (inferInstance : MeasurableSpace O).comap
        (fun ω : S × N => observe (ω.1, hist ω.2))] =ᵐ[μ.prod P]
      fun _ => ∫ ω, f (Q ω) ∂P := by
  have hnoise : Measurable (fun ω : S × N => f (Q ω.2)) :=
    hf.comp (hQ.comp measurable_snd)
  have hobs : Measurable (fun ω : S × N => observe (ω.1, hist ω.2)) :=
    hobserve.comp (measurable_fst.prodMk (hhist.comp measurable_snd))
  have hi := (indepFun_snd_observation (μ := μ) hQ hhist hind observe hobserve).comp
    hf measurable_id
  have hc := condExp_indep_eq hnoise.comap_le hobs.comap_le
    (comap_measurable (fun ω : S × N => f (Q ω.2))).stronglyMeasurable hi
  have hint : (∫ ω : S × N, f (Q ω.2) ∂μ.prod P) = ∫ ω, f (Q ω) ∂P := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := μ) (ν := P) (fun ω => f (Q ω)))
  simpa only [hint] using hc

theorem condExp_snd_observation_eq_zero {Q : N → ℝ} {hist : N → H}
    (hQ : Measurable Q) (hhist : Measurable hist)
    (hind : IndepFun Q hist P) (observe : S × H → O)
    (hobserve : Measurable observe) (hmean : ∫ ω, Q ω ∂P = 0) :
    (μ.prod P)[(fun ω : S × N => Q ω.2) |
      (inferInstance : MeasurableSpace O).comap
        (fun ω : S × N => observe (ω.1, hist ω.2))] =ᵐ[μ.prod P]
      fun _ => 0 := by
  simpa only [id_eq, hmean] using
    condExp_snd_observation (μ := μ) hQ hhist hind observe hobserve id measurable_id

theorem brownian_increment_indep_observation
    {B : ℝ≥0 → N → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, Measurable (B t)) {X : S → ℝ} (hX : Measurable X)
    (t u : ℝ≥0) :
    IndepFun (fun ω : S × N => B (t + u) ω.2 - B t ω.2)
      (fun ω : S × N => fun s : Set.Iic t => (s.1 : ℝ) * X ω.1 + B s.1 ω.2)
      (μ.prod P) := by
  have hind : IndepFun (fun ω => B (t + u) ω - B t ω)
      (fun ω => fun s : Set.Iic t => B s.1 ω) P :=
    (hB.indepFun_shift t).comp (measurable_pi_apply u) measurable_id
  exact indepFun_snd_observation (μ := μ) ((hmB _).sub (hmB _))
    (Measurable.of_eval (fun s => hmB s.1)) hind
    (fun p : S × (Set.Iic t → ℝ) => fun s => (s.1 : ℝ) * X p.1 + p.2 s)
    (Measurable.of_eval (fun s =>
      (measurable_const.mul (hX.comp measurable_fst)).add
        ((measurable_pi_apply s).comp measurable_snd)))

theorem brownian_increment_condExp_observation
    {B : ℝ≥0 → N → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, Measurable (B t)) {X : S → ℝ} (hX : Measurable X)
    (t u : ℝ≥0) :
    (μ.prod P)[(fun ω : S × N => B (t + u) ω.2 - B t ω.2) |
      (inferInstance : MeasurableSpace (Set.Iic t → ℝ)).comap
        (fun ω : S × N => fun s : Set.Iic t => (s.1 : ℝ) * X ω.1 + B s.1 ω.2)]
      =ᵐ[μ.prod P] fun _ => 0 := by
  have hind : IndepFun (fun ω => B (t + u) ω - B t ω)
      (fun ω => fun s : Set.Iic t => B s.1 ω) P :=
    (hB.indepFun_shift t).comp (measurable_pi_apply u) measurable_id
  apply condExp_snd_observation_eq_zero (μ := μ) ((hmB _).sub (hmB _))
    (Measurable.of_eval (fun s => hmB s.1)) hind
    (fun p : S × (Set.Iic t → ℝ) => fun s => (s.1 : ℝ) * X p.1 + p.2 s)
    (Measurable.of_eval (fun s =>
      (measurable_const.mul (hX.comp measurable_fst)).add
        ((measurable_pi_apply s).comp measurable_snd)))
  change (∫ ω, B (t + u) ω - B t ω ∂P) = 0
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
    hB.integral_eval, hB.integral_eval, sub_self]

end Problem336AdditiveD139.NoisePast

end

end OAI
