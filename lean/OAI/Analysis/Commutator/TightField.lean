import Mathlib
import OAI.Analysis.Commutator.FieldAlgebra

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

omit [CompleteSpace H] [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma operator_bound_irrel (T : Ω → H →L[ℂ] H)
    (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
    {b c : ℝ} (hb : ∀ᵐ a ∂μ,‖T a‖≤b) (hc : ∀ᵐ a ∂μ,‖T a‖≤c) :
    operator μ T hm hb=operator μ T hm hc := by
  apply operator_eq_of_ae_apply
  exact operator_ae μ T hm hb

lemma fieldMember_tight (Q : Ω → VonNeumannAlgebra H)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    {c : ℝ} (hc : 0≤c) (hAc : ‖A‖≤c) :
    ∃ (T : Ω → H →L[ℂ] H) (hm : ∀ ξ,AEStronglyMeasurable (fun a => T a ξ) μ)
      (hb : ∀ᵐ a ∂μ,‖T a‖≤c),A=operator μ T hm hb ∧ ∀ᵐ a ∂μ,T a∈Q a := by
  obtain ⟨T,hm,b,hb,hb0,rfl,hmem⟩ := hA
  have hb' := (operator_norm_le_iff_ae μ T hm hb hc).mp hAc
  exact ⟨T,hm,hb',operator_bound_irrel μ T hm hb hb',hmem⟩

omit [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H] in
lemma fieldMember_commutes_indicator (Q : Ω → VonNeumannAlgebra H)
    {A : Lp H 2 μ →L[ℂ] Lp H 2 μ} (hA : FieldMember μ Q A)
    (s : Set Ω) (hs : MeasurableSet s) : Commute A (indicatorOperator μ s hs) := by
  obtain ⟨T,hm,b,hb,_,rfl,_⟩ := hA
  exact operator_commutes_indicator μ T hm hb s hs

end Kadison.Decomposable

end

end
end

end OAI
