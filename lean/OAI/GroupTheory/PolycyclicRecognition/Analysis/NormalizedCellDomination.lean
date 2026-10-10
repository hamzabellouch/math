import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceCellProfiles
import Mathlib.Dynamics.Ergodic.MeasurePreserving

namespace OAI

/-! # Domination of normalized cell laws under Haar-preserving maps -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- If the inverse image of the smaller cell lies in the sampling cell,
the pushed normalized sampling law dominates its normalized restriction.
The loss is exactly the ratio of the two Haar volumes. -/
theorem normalized_cell_transport_domination
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (C D : Set X) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞)
    (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (τ : X → X) (hτ : MeasurePreserving τ μ μ)
    (hcover : τ ⁻¹' C ⊆ D)
    (S : Set X) (hS : MeasurableSet S) :
    (cellProbabilityMeasure μ C hC0 hCfin : Measure X) S ≤
      (μ D / μ C) * (cellProbabilityMeasure μ D hD0 hDfin : Measure X) (τ ⁻¹' S) := by
  have hm : μ (S ∩ C) ≤ μ (τ ⁻¹' S ∩ D) := calc
    μ (S ∩ C) = μ (τ ⁻¹' (S ∩ C)) :=
      (hτ.measure_preimage (hS.inter hC).nullMeasurableSet).symm
    _ ≤ μ (τ ⁻¹' S ∩ D) := measure_mono (fun _ hx => ⟨hx.1, hcover hx.2⟩)
  change (((μ C)⁻¹ • μ.restrict C) S) ≤
    (μ D / μ C) * (((μ D)⁻¹ • μ.restrict D) (τ ⁻¹' S))
  rw [Measure.smul_apply, Measure.smul_apply, Measure.restrict_apply hS,
    Measure.restrict_apply (hτ.measurable hS)]
  change (μ C)⁻¹ * μ (S ∩ C) ≤
    (μ D / μ C) * ((μ D)⁻¹ * μ (τ ⁻¹' S ∩ D))
  calc
    _ ≤ (μ C)⁻¹ * μ (τ ⁻¹' S ∩ D) := mul_le_mul' le_rfl hm
    _ = _ := by
      rw [div_eq_mul_inv]
      have he : μ D * (μ C)⁻¹ * ((μ D)⁻¹ * μ (τ ⁻¹' S ∩ D)) =
          (μ C)⁻¹ * (μ D * (μ D)⁻¹) * μ (τ ⁻¹' S ∩ D) := by ac_rfl
      rw [he, ENNReal.mul_inv_cancel hD0 hDfin, mul_one]

end PolycyclicRecognition

end OAI
