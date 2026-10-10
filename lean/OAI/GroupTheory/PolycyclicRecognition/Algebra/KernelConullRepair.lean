import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace OAI

/-! # Repairing a probability kernel on a null set of parameters -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory ProbabilityTheory Set Filter

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (ν : Measure Y) [IsProbabilityMeasure ν] (κ : Kernel Y X) [IsMarkovKernel κ]

theorem exists_kernel_conull_repair (P : Measure X → Prop)
    (hP : ∀ᵐ y ∂ν, P (κ y)) :
    ∃ k : Y → Measure X, Measurable k ∧
      (∀ y, IsProbabilityMeasure (k y) ∧ P (k y)) ∧ k =ᵐ[ν] κ := by
  classical
  let T := toMeasurable ν {y | ¬P (κ y)}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT : ν T = 0 := (measure_toMeasurable _).trans (ae_iff.mp hP)
  have hae : ∀ᵐ y ∂ν, y ∉ T := measure_eq_zero_iff_ae_notMem.mp hT
  obtain ⟨y₀, hy₀⟩ := hae.exists
  have h₀ : P (κ y₀) := by
    by_contra h
    exact hy₀ (subset_toMeasurable ν _ h)
  let k : Y → Measure X := T.piecewise (fun _ => κ y₀) κ
  refine ⟨k, measurable_const.piecewise hTm κ.measurable, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ T
    · simpa only [k, piecewise_eq_of_mem T _ _ hy] using
        (show IsProbabilityMeasure (κ y₀) ∧ P (κ y₀) from ⟨inferInstance, h₀⟩)
    · have h : P (κ y) := by
        by_contra h
        exact hy (subset_toMeasurable ν _ h)
      simpa only [k, piecewise_eq_of_notMem T _ _ hy] using
        (show IsProbabilityMeasure (κ y) ∧ P (κ y) from ⟨inferInstance, h⟩)
  · filter_upwards [hae] with y hy
    exact piecewise_eq_of_notMem T _ _ hy

end PolycyclicRecognition

end

end OAI
