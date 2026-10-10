import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationPosteriorStep

namespace OAI

section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Compact
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : Ω → Position → ℝ} {R : ℝ}

lemma compact_random_field_integrable
    (hm : Measurable (Function.uncurry f))
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C)
    (hs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → f o x=0) :
    Integrable (Function.uncurry f) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb R
  let g := (Metric.closedBall (0:Position) R).indicator (fun _ => max C 0)
  have hgm : Measurable g := measurable_const.indicator measurableSet_closedBall
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (C:=max C 0) (isCompact_closedBall (0:Position) R).measure_ne_top)
  apply (hgi.comp_snd P).mono' hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm (hgm.comp measurable_snd))).2
  filter_upwards [hs] with o ho
  apply Eventually.of_forall
  intro x
  change ‖f o x‖≤g x
  by_cases hx : x∈Metric.closedBall (0:Position) R
  · simpa only [g,Set.indicator_of_mem hx,Real.norm_eq_abs] using (hC o x hx).trans (le_max_left C 0)
  · have hRx : R≤‖x‖ := le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx)
    simp only [ho x hRx,g,Set.indicator_of_notMem hx,norm_zero,le_refl]

lemma PropagationDatum.error_product_integrable {B C r Z L : ℝ} {μ : Ω → Position → ℝ}
    (d : PropagationDatum P B C r Z L μ) :
    Integrable (Function.uncurry d.error) (P.prod volume) :=
  compact_random_field_integrable d.error_measurable d.error_bounds
    (d.invariant.mono (fun _ h => h.error_support))
end Compact

section Posterior
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → Position → ℝ} {R : ℝ}
variable (obs : Ω → A) (ho : Measurable obs)

include ho
lemma posteriorAverage_support_ae (hs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → f o x=0) :
    ∀ᵐ o ∂P,∀ x,R≤‖x‖ → posteriorAverage P obs f (obs o) x=0 := by
  filter_upwards [posterior_ae P obs ho hs] with o hoi
  intro x hx
  exact integral_eq_zero_of_ae (hoi.mono (fun v hv => hv x hx))

lemma posteriorAverage_integral (hm : Measurable (Function.uncurry f))
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C) (x : Position) :
    (∫ o,posteriorAverage P obs f (obs o) x ∂P)=∫ o,f o x ∂P := by
  have he := ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id ho
    (integrable_section_of_ball_bounds (μ:=P) hm hb x)
  calc
    _ = ∫ o,P[fun v => f v x | MeasurableSpace.comap obs inferInstance] o ∂P := integral_congr_ae he.symm
    _ = _ := integral_condExp ho.comap_le

lemma posteriorAverage_total_integral (hm : Measurable (Function.uncurry f))
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C)
    (hs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → f o x=0) :
    (∫ o,(∫ x,posteriorAverage P obs f (obs o) x) ∂P)=∫ o,(∫ x,f o x) ∂P := by
  have hm' : Measurable (fun z : Ω×Position => posteriorAverage P obs f (obs z.1) z.2) :=
    (posteriorAverage_joint_measurable P obs hm).comp (ho.prodMap measurable_id)
  have hb' : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |posteriorAverage P obs f (obs o) x|≤C := by
    intro D
    obtain ⟨C,hC⟩ := posteriorAverage_uniform_bounds P obs hb D
    exact ⟨C,fun o => hC (obs o)⟩
  have hi := compact_random_field_integrable hm hb hs
  have hi' := compact_random_field_integrable hm' hb' (posteriorAverage_support_ae obs ho hs)
  rw [integral_integral_swap hi',integral_integral_swap hi]
  exact integral_congr_ae (Eventually.of_forall (fun x => posteriorAverage_integral obs ho hm hb x))
end Posterior
end NeutralAtom
end

end

end OAI
