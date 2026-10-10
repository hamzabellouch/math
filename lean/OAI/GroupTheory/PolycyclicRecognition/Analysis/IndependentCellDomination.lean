import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedCellDomination
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Independent ordinary charts are dominated by independent suffix sampling -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Integrate the conditional normalized-cell comparison in the starting
point. The cost is the exact larger-to-smaller Haar-volume ratio. -/
theorem independent_cell_pair_domination
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (C D : Set X) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞)
    (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (τ : X → X → X)
    (hτ : ∀ a ∈ C, MeasurePreserving (τ a) μ μ)
    (hcover : ∀ a ∈ C, (τ a) ⁻¹' C ⊆ D)
    (hpair : Measurable (fun p : X × X => (p.1, τ p.1 p.2)))
    (B : Set (X × X)) (hB : MeasurableSet B) :
    (cellProbabilityMeasure μ C hC0 hCfin : Measure X).prod
        (cellProbabilityMeasure μ C hC0 hCfin : Measure X) B ≤
      (μ D / μ C) * (cellProbabilityMeasure μ C hC0 hCfin : Measure X).prod
        (cellProbabilityMeasure μ D hD0 hDfin : Measure X)
        ((fun p : X × X => (p.1, τ p.1 p.2)) ⁻¹' B) := by
  let P := (fun p : X × X => (p.1, τ p.1 p.2)) ⁻¹' B
  have hP : MeasurableSet P := hpair hB
  rw [Measure.prod_apply hB, Measure.prod_apply hP]
  calc
    _ ≤ ∫⁻ a, (μ D / μ C) *
        (cellProbabilityMeasure μ D hD0 hDfin : Measure X) (Prod.mk a ⁻¹' P)
        ∂(cellProbabilityMeasure μ C hC0 hCfin : Measure X) := by
      apply lintegral_mono_ae
      filter_upwards [ae_mem_cellProbabilityMeasure μ C hC hC0 hCfin] with a ha
      exact normalized_cell_transport_domination μ C D hC hC0 hCfin hD0 hDfin
        (τ a) (hτ a ha) (hcover a ha) (Prod.mk a ⁻¹' B)
        ((measurable_const.prodMk measurable_id) hB)
    _ = _ := lintegral_const_mul _ (measurable_measure_prodMk_left hP)

end PolycyclicRecognition

end OAI
