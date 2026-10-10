import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteFiberMass

namespace OAI

/-! # Large sections inside a finite rectangle -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem exists_large_sections_in_rectangle (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (U : Set X) (V : Set Y)
    (hU : MeasurableSet U)
    (hUfin : μ U ≠ ∞) (hVfin : ν V ≠ ∞)
    (hUpos : 0 < (μ U).toReal) (hVpos : 0 < (ν V).toReal)
    (S : Set (X × Y)) (hS : MeasurableSet S) (hsub : S ⊆ U ×ˢ V)
    (hm : 0 < (μ.prod ν S).toReal) :
    ∃ A : Set X, MeasurableSet A ∧ A ⊆ U ∧
      (μ.prod ν S).toReal / (2 * (ν V).toReal) ≤ (μ A).toReal ∧
      ∀ x ∈ A,
        (μ.prod ν S).toReal / (2 * (μ U).toReal) ≤
          (ν (Prod.mk x ⁻¹' S)).toReal := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa using hUfin.lt_top⟩
  let : IsFiniteMeasure (ν.restrict V) := ⟨by simpa using hVfin.lt_top⟩
  have hprod : (μ.restrict U).prod (ν.restrict V) S = μ.prod ν S := by
    rw [Measure.prod_restrict, Measure.restrict_apply hS, inter_eq_left.2 hsub]
  obtain ⟨A, hA, hmass, hfiber⟩ := exists_large_sections
    (μ.restrict U) (ν.restrict V) (by simpa using hUpos) (by simpa using hVpos)
    S hS (by simpa only [hprod] using hm)
  refine ⟨A ∩ U, hA.inter hU, inter_subset_right, ?_, ?_⟩
  · simpa only [hprod, Measure.restrict_apply hA, Measure.restrict_apply_univ] using hmass
  · intro x hx
    have hsV : Prod.mk x ⁻¹' S ⊆ V := fun y hy => (hsub hy).2
    have hmeas : MeasurableSet (Prod.mk x ⁻¹' S) := hS.preimage measurable_prodMk_left
    simpa only [hprod, Measure.restrict_apply_univ, Measure.restrict_apply hmeas,
      inter_eq_left.2 hsV] using hfiber x hx.1

end PolycyclicRecognition

end

end OAI
