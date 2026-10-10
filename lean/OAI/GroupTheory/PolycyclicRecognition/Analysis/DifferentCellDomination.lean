import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedCellDomination
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Density comparison with different starting and target cells -/

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- The starting law is arbitrary. Only the target-to-suffix volume ratio
enters the domination constant, including when the two scales differ. -/
theorem different_cell_pair_domination
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : ProbabilityMeasure X) (A : Set X)
    (hA : ∀ᵐ a ∂(ν : Measure X), a ∈ A)
    (μ : Measure Y) (C D : Set Y) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (τ : X → Y → Y)
    (hτ : ∀ a ∈ A, MeasurePreserving (τ a) μ μ)
    (hcover : ∀ a ∈ A, (τ a) ⁻¹' C ⊆ D)
    (hpair : Measurable (fun p : X × Y => (p.1, τ p.1 p.2)))
    (B : Set (X × Y)) (hB : MeasurableSet B) :
    (ν : Measure X).prod (cellProbabilityMeasure μ C hC0 hCfin : Measure Y) B ≤
      (μ D / μ C) * (ν : Measure X).prod
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y)
        ((fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' B) := by
  let P := (fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' B
  have hP : MeasurableSet P := hpair hB
  rw [Measure.prod_apply hB, Measure.prod_apply hP]
  calc
    _ ≤ ∫⁻ a, (μ D / μ C) *
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y) (Prod.mk a ⁻¹' P)
        ∂(ν : Measure X) := by
      apply lintegral_mono_ae
      filter_upwards [hA] with a ha
      exact normalized_cell_transport_domination μ C D hC hC0 hCfin hD0 hDfin
        (τ a) (hτ a ha) (hcover a ha) (Prod.mk a ⁻¹' B)
        ((measurable_const.prodMk measurable_id) hB)
    _ = _ := lintegral_const_mul _ (measurable_measure_prodMk_left hP)

end PolycyclicRecognition

end OAI
