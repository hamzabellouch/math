import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationPosteriorStep
import OAI.Analysis.CoulombRadii.RandomFields.CompactRandomField

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom
lemma barrierSource_eq_propagationRHS (r : ℝ) (u μ p : Position → ℝ) (x : Position) :
    barrierSource r u μ p x = propagationRHS r ‖x‖ (μ x) (p x) (u x) := by
  unfold barrierSource cutoffReaction propagationRHS propagationCoreSource
  simp only [Set.indicator_apply,Set.mem_ofPred_eq]
  ring

theorem PropagationDatum.valid_event {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B C r Z L M : ℝ}
    {μ : Ω → Position → ℝ} (d : PropagationDatum P B C r Z L μ)
    (hcost : (∫ o,(∫ x,d.error o x) ∂P) ≤ M) :
    ∃ V : Set Ω,MeasurableSet V ∧ P.real Vᶜ ≤ M ∧
      ∀ o∈V,PropagationInvariant B C r Z L (d.offset o) (μ o) (d.error o) ∧
        Integrable (d.error o) ∧ (∫ x,d.error o x) ≤ 1 := by
  let bad := {o | ¬(PropagationInvariant B C r Z L (d.offset o) (μ o) (d.error o) ∧ Integrable (d.error o))}
  have hbad : P bad = 0 := by
    apply ae_iff.mp
    filter_upwards [d.invariant,d.error_product_integrable.prod_right_ae] with o ho hi
    exact ⟨ho,hi⟩
  let W := (toMeasurable P bad)ᶜ
  have hW : MeasurableSet W := (measurableSet_toMeasurable P bad).compl
  have hWzero : P.real Wᶜ = 0 := by simp only [W,compl_compl,Measure.real,measure_toMeasurable,hbad,ENNReal.toReal_zero]
  let X := fun o => ∫ x,d.error o x
  have hXm : Measurable X := d.error_measurable.stronglyMeasurable.integral_prod_right.measurable
  have hXi : Integrable X P := d.error_product_integrable.integral_prod_left
  have hXp : 0 ≤ᵐ[P] X := d.invariant.mono (fun o ho => integral_nonneg ho.nonnegative_error)
  let A := {o | X o ≤ 1}
  have hA : MeasurableSet A := measurableSet_le hXm measurable_const
  have hAp : P.real Aᶜ ≤ M := by
    calc
      P.real Aᶜ ≤ P.real {o | 1 ≤ X o} := measureReal_mono (by intro o ho; change ¬ X o ≤ 1 at ho; exact (lt_of_not_ge ho).le)
      _ ≤ ∫ o,X o ∂P := by simpa only [one_mul] using mul_meas_ge_le_integral_of_nonneg hXp hXi 1
      _ ≤ M := hcost
  refine ⟨W∩A,hW.inter hA,?_,?_⟩
  · rw [compl_inter]
    exact (measureReal_union_le _ _).trans (by simpa only [hWzero,zero_add] using add_le_add (le_refl (P.real Wᶜ)) hAp)
  · intro o ho
    have hb : o∉bad := fun hb => ho.1 (subset_toMeasurable P bad hb)
    exact ⟨(not_not.mp hb).1,(not_not.mp hb).2,ho.2⟩

lemma PropagationDatum.error_global_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B C r Z L : ℝ} {μ : Ω → Position → ℝ}
    (d : PropagationDatum P B C r Z L μ) :
    ∃ A : ℝ,∀ o,PropagationInvariant B C r Z L (d.offset o) (μ o) (d.error o) →
      ∀ x,d.error o x ≤ A := by
  obtain ⟨A,hA⟩ := d.error_bounds r
  refine ⟨max A 0,?_⟩
  intro o ho x
  by_cases hx : ‖x‖ ≤ r
  · exact (le_abs_self _).trans ((hA o x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)).trans (le_max_left _ _))
  · rw [ho.error_support x (le_of_not_ge hx)]
    exact le_max_right _ _
end NeutralAtom
end

end

end OAI
