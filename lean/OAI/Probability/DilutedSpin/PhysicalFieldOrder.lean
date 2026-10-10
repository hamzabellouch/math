import OAI.Probability.DilutedSpin.FunctionalContinuity
import OAI.Probability.DilutedSpin.IntegralError

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {p N : ℕ} [NeZero N]

noncomputable def centeredDisorderAt (M : Model p) (k : ℕ) (h : Fin N → ℝ) : ℝ :=
  ∫ z : Fin k → InteractionSample p,indexAverage z h-(N:ℝ)*Real.log 2
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)

lemma centeredDisorderAt_bound (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (k : ℕ) (h : Fin N → ℝ) :
    |centeredDisorderAt M k h|≤k*interactionMoment M+∑ i,|h i| := by
  have hb := norm_integral_le_of_norm_le (f := fun z : Fin k → InteractionSample p =>
      indexAverage z h-(N:ℝ)*Real.log 2)
    ((interaction_sum_integrable M hθ k).add (integrable_const (∑ i,|h i|)))
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using (indexAverage_bound (NeZero.pos N) z h)))
  simpa only [centeredDisorderAt,Real.norm_eq_abs,Pi.add_apply,
    integral_add (interaction_sum_integrable M hθ k) (integrable_const _),
    integral_const,probReal_univ,one_smul,integral_interaction_sum M hθ k,interactionMoment] using hb

omit [NeZero N] in
lemma centeredDisorderAt_measurable (M : Model p) (k : ℕ) :
    Measurable (centeredDisorderAt (N := N) M k) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  exact ((continuous_indexAverage (p := p) (k := k) (N := N)).sub continuous_const).stronglyMeasurable.integral_prod_left.measurable

lemma centeredIndex_integrable_prod (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    Integrable (fun z : (Fin k → InteractionSample p)×(Fin N → ℝ) =>
      indexAverage z.1 z.2-(N:ℝ)*Real.log 2)
      ((Measure.pi (fun _ : Fin k => M.disorder.toMeasure)).prod
        (Measure.pi (fun _ : Fin N => M.field.toMeasure))) := by
  let : OpensMeasurableSpace (Fin k → InteractionSample p) := Pi.opensMeasurableSpace
  apply (((interaction_sum_integrable M hθ k).comp_fst _).add
    ((integrable_pi_sum M.field.toMeasure hh).comp_snd _)).mono'
    ((continuous_indexAverage (p := p) (k := k) (N := N)).sub continuous_const).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using (indexAverage_bound (NeZero.pos N) z.1 z.2))

lemma centeredDisorderAt_integral (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (k : ℕ) :
    (∫ h : Fin N → ℝ,centeredDisorderAt M k h ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
      disorderAverage M N k-(N:ℝ)*Real.log 2 := by
  simp only [centeredDisorderAt]
  rw [← integral_integral_swap (centeredIndex_integrable_prod M hθ hh k)]
  simp_rw [integral_sub (indexAverage_integrable_and_fieldAverage_bound M hh (NeZero.pos N) _).1
    (integrable_const _),integral_const,probReal_univ,one_smul]
  simpa only [fieldAverage,disorderAverage,integral_const,probReal_univ,one_smul] using
    (integral_sub (fieldAverage_integrable_and_disorderAverage_bound M hθ hh (NeZero.pos N) k).1
      (integrable_const ((N:ℝ)*Real.log 2)))

lemma centeredDisorderAt_joint_integrable (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) (r : ℝ≥0) :
    Integrable (fun z : ℕ×(Fin N → ℝ) => centeredDisorderAt M z.1 z.2)
      ((poissonMeasure r).prod (Measure.pi (fun _ : Fin N => M.field.toMeasure))) := by
  apply ((((poisson_integrable_count r).mul_const (interactionMoment M)).comp_fst _).add
    ((integrable_pi_sum M.field.toMeasure hh).comp_snd _)).mono'
  · exact (measurable_from_prod_countable_right (fun k => centeredDisorderAt_measurable M k)).aestronglyMeasurable
  · exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Pi.add_apply] using (centeredDisorderAt_bound M hθ z.1 z.2))

lemma centeredPressure_field_order (M : Model p)
    (hθ : Integrable (fun a : InteractionSample p => ‖a.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    (∫ h : Fin N → ℝ,∫ k,centeredDisorderAt M k h ∂poissonMeasure (M.alpha*N)
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))=
        (N:ℝ)*(pressure M N-Real.log 2) := by
  rw [← integral_integral_swap (centeredDisorderAt_joint_integrable M hθ hh (M.alpha*N))]
  simp_rw [centeredDisorderAt_integral M hθ hh]
  rw [integral_sub (disorderAverage_integrable_and_pressure_bound M hθ hh (NeZero.pos N)).1
    (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  change (∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))-(N:ℝ)*Real.log 2=
    (N:ℝ)*((∫ k,disorderAverage M N k ∂poissonMeasure (M.alpha*N))/(N:ℝ)-Real.log 2)
  have hN : (N:ℝ)≠0 := by exact_mod_cast NeZero.ne N
  field_simp

end DilutedSpinGlass

end

end OAI
