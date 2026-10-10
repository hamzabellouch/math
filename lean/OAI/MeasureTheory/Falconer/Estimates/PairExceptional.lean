import OAI.MeasureTheory.Falconer.Estimates.ClassBadRecombination

namespace OAI

/-! # Two-sided exceptional sets measured on the original pair -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

def pairExceptional (A B : Set (Space d)) (D E : Set (Space d × Space d)) :
    Set (Space d × Space d) :=
  ((Aᶜ ×ˢ univ) ∪ (univ ×ˢ Bᶜ)) ∪ D ∪ Prod.swap ⁻¹' E

theorem pairExceptional_measurable {A B : Set (Space d)} {D E : Set (Space d × Space d)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hD : MeasurableSet D) (hE : MeasurableSet E) :
    MeasurableSet (pairExceptional A B D E) :=
  (((hA.compl.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hB.compl)).union hD).union
    (hE.preimage measurable_swap)

theorem pairExceptional_outside {A B : Set (Space d)} {D E : Set (Space d × Space d)}
    {z : Space d × Space d} (hz : z ∉ pairExceptional A B D E) :
    z.1 ∈ A ∧ z.2 ∈ B ∧ z ∉ D ∧ z.swap ∉ E := by
  classical
  simp only [pairExceptional,mem_union,not_or,mem_prod,mem_compl_iff,mem_univ,true_and,
    and_true,not_not,mem_preimage] at hz
  exact ⟨hz.1.1.1,hz.1.1.2,hz.1.2,hz.2⟩

theorem pairExceptional_mass (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A B : Set (Space d)) (D E : Set (Space d × Space d)) (hE : MeasurableSet E) :
    (μ.prod ν) (pairExceptional A B D E) ≤
      μ Aᶜ + ν Bᶜ + (μ.prod ν) D + (ν.prod μ) E := by
  apply (measure_union_le _ _).trans
  apply add_le_add ?_ ?_
  · apply (measure_union_le _ _).trans
    apply add_le_add ?_ le_rfl
    apply (measure_union_le _ _).trans
    simp only [Measure.prod_prod,measure_univ,mul_one,one_mul]
    exact le_rfl
  · exact le_of_eq ((Measure.measurePreserving_swap (μ := μ) (ν := ν)).measure_preimage hE.nullMeasurableSet)

end Falconer

end OAI
