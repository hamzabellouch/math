import Mathlib
import OAI.Analysis.Commutator.DiagonalCommute
import OAI.Analysis.Commutator.FieldAdjoint
import OAI.Analysis.Commutator.ScalarIndicatorAdjoint

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma adjoint_measurable (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    ∀ ξ,AEStronglyMeasurable (fun a => (T a).adjoint ξ) μ := by
  let A := operator μ T hm hb
  have hcomm (s : Set Ω) (hs : MeasurableSet s) :
      Commute A.adjoint (indicatorOperator μ s hs) := by
    have h := congrArg star (operator_commutes_indicator μ T hm hb s hs).symm
    change A.adjoint*indicatorOperator μ s hs=indicatorOperator μ s hs*A.adjoint
    simpa only [A,star_mul,(indicatorOperator_selfAdjoint (H:=H) μ s hs).star_eq,ContinuousLinearMap.star_eq_adjoint] using h
  obtain ⟨U,hU,hUb,he⟩ := exists_field_of_commutes_indicator μ A.adjoint hcomm
  have hea := adjoint_ae μ T U hm hU hb hUb he.symm
  intro ξ
  apply (hU ξ).congr
  filter_upwards [hea] with a ha
  rw [ha]

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma adjoint_field_bound (T : Ω → H →L[ℂ] H)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) : ∀ᵐ a ∂μ,‖(T a).adjoint‖≤b := by
  simpa only [←ContinuousLinearMap.star_eq_adjoint,norm_star] using hb

lemma operator_adjoint (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) :
    operator μ (fun a => (T a).adjoint) (adjoint_measurable μ T hm hb)
      (adjoint_field_bound μ T hb)=(operator μ T hm hb).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [operator_ae μ (fun a => (T a).adjoint) (adjoint_measurable μ T hm hb)
    (adjoint_field_bound μ T hb) f,operator_ae μ T hm hb g] with a ha ht
  rw [ha,ht,ContinuousLinearMap.adjoint_inner_left]

end Kadison.Decomposable

end

end
end

end OAI
