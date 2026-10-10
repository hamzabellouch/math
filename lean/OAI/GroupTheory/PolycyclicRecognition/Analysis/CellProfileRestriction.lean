import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedProbabilityRestriction

namespace OAI

/-! # Restricting profile samples to their actual carrying cell -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- The normalized cell measure is carried by the cell itself. -/
theorem ae_mem_cellProbabilityMeasure {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (C : Set A) (hC : MeasurableSet C) (hC0 : μ C ≠ 0) (hCfin : μ C ≠ ⊤) :
    ∀ᵐ a ∂(cellProbabilityMeasure μ C hC0 hCfin : Measure A), a ∈ C :=
  Measure.ae_smul_measure (ae_restrict_mem hC) _

/-- Restricting a sample to a measurable set of full probability does not
change any pushed-forward profile law. -/
theorem map_supportedProbabilityRestriction
    {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (C : Set A) (hC : MeasurableSet C)
    (hfull : ∀ᵐ a ∂(μ : Measure A), a ∈ C) (f : A → X) (hf : Measurable f) :
    ProbabilityMeasure.map (supportedProbabilityRestriction μ C hC hfull)
      (fun a : C => f a.val) = ProbabilityMeasure.map μ f := by
  apply Subtype.ext
  have h := Measure.map_map (μ := (supportedProbabilityRestriction μ C hC hfull : Measure C))
    hf (measurable_subtype_coe : Measurable (Subtype.val : C → A))
  rw [supportedProbabilityRestriction_map] at h
  exact h.symm

end PolycyclicRecognition

end

end OAI
