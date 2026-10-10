import OAI.GroupTheory.PolycyclicRecognition.Analysis.DifferentCellDomination

namespace OAI

/-! # A changed Haar cell dominated by independent suffix sampling -/

namespace PolycyclicRecognition
open MeasureTheory Set
open scoped ENNReal

/-- A measure-preserving change of the target cell is dominated by the
independent starting-cell and suffix law. The inverse-cover inclusion supplies
the required geometric hypothesis. -/
theorem translated_cell_domination
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : ProbabilityMeasure X) (A : Set X)
    (hA : ∀ᵐ a ∂(ν : Measure X), a ∈ A)
    (μ : Measure Y) (C D : Set Y) (hC : MeasurableSet C)
    (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ∞) (hD0 : μ D ≠ 0) (hDfin : μ D ≠ ∞)
    (ψ : Y → Y) (hψ : Measurable ψ) (τ : X → Y → Y) (m : X → Y → Y)
    (hτ : ∀ a ∈ A, MeasurePreserving (τ a) μ μ)
    (hcover : ∀ a ∈ A, (τ a) ⁻¹' C ⊆ D)
    (hpair : Measurable (fun p : X × Y => (p.1, τ p.1 p.2)))
    (hmatch : ∀ a k, ψ (τ a k) = m a k)
    (S : Set Y) (hS : MeasurableSet S) :
    (cellProbabilityMeasure μ C hC0 hCfin : Measure Y) (ψ ⁻¹' S) ≤
      (μ D / μ C) * (ν : Measure X).prod
        (cellProbabilityMeasure μ D hD0 hDfin : Measure Y)
        {p | m p.1 p.2 ∈ S} := by
  have hh := different_cell_pair_domination ν A hA μ C D hC hC0 hCfin hD0 hDfin
    τ hτ hcover hpair (univ ×ˢ (ψ ⁻¹' S)) (MeasurableSet.univ.prod (hψ hS))
  have he : (fun p : X × Y => (p.1, τ p.1 p.2)) ⁻¹' (univ ×ˢ (ψ ⁻¹' S)) =
      {p | m p.1 p.2 ∈ S} := by
    ext p
    simp only [mem_preimage, mem_prod, mem_univ, true_and, hmatch, mem_ofPred_eq]
  simpa only [Measure.prod_prod, measure_univ, one_mul, he] using hh

end PolycyclicRecognition

end OAI
