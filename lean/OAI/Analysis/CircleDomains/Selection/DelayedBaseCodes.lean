import OAI.Analysis.CircleDomains.Probability.PathCostMeasure
import OAI.Analysis.CircleDomains.Probability.DelayedTupleMeasure

namespace OAI

/-! Retagging preserves the complete base-code conditions and cost finiteness.
It is a Borel operation on the actual code space. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_delay (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (N : ℕ) {Γ : TaggedPath X} (hΓ : AllowedTaggedPath d ν T Γ) :
    AllowedTaggedPath d ν T (delayTaggedPath N Γ) := by
  refine ⟨hΓ.1, tagRules_delay d.levels T N hΓ.2.1, ?_, ?_, ?_⟩
  · exact (residualConstraintFamily_delay _ _ _ _ _ N Γ).mpr hΓ.2.2.1
  · exact (residualConstraintFamily_delay _ _ _ _ _ N Γ).mpr hΓ.2.2.2.1
  · rw [residualImage_delay]
    exact hΓ.2.2.2.2

theorem endpointCode_delay (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (N : ℕ) {Γ : TaggedPath X} (hΓ : EndpointCode d ν T Γ) :
    EndpointCode d ν T (delayTaggedPath N Γ) :=
  ⟨allowedTaggedPath_delay d ν T N hΓ.1, hΓ.2⟩

def delayBaseCode (d : PathCodeData X Y) (N : ℕ) (Γ : BasePathCode d) : BasePathCode d :=
  ⟨delayTaggedPath N Γ.val, endpointCode_delay d 0 (fun _ _ => ∅) N Γ.property⟩

variable [BorelSpace C(PathTime, X)]

theorem measurable_delayBaseCode (d : PathCodeData X Y) (N : ℕ) :
    Measurable (delayBaseCode d N) :=
  (((continuous_delayTaggedPath N).measurable).comp measurable_subtype_coe).subtype_mk

variable {D : Type*} [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [BorelSpace C(PathTime, X)] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem baseCodeOccupation_delay (d : PathCodeData X Y) (N : ℕ) (Γ : BasePathCode d) :
    baseCodeOccupation d (delayBaseCode d N Γ) = baseCodeOccupation d Γ := rfl

omit [BorelSpace C(PathTime, X)] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem pathCostMeasure_delay_finite_iff (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (N : ℕ) (Γ : BasePathCode d) :
    pathCostMeasure d p c (delayBaseCode d N Γ) univ < ∞ ↔
      pathCostMeasure d p c Γ univ < ∞ := by
  rw [pathCostMeasure_finite_iff, pathCostMeasure_finite_iff]
  rfl

variable [SecondCountableTopology X] [Countable D]

def delayFiniteCostCode (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (N : ℕ) (Γ : FiniteCostCode d p c) : FiniteCostCode d p c :=
  ⟨delayBaseCode d N Γ.val, (pathCostMeasure_delay_finite_iff d p c N Γ.val).mpr Γ.property⟩

omit [SecondCountableTopology X] [Countable D] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_delayFiniteCostCode (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (N : ℕ) :
    Measurable (delayFiniteCostCode d p c N) :=
  ((measurable_delayBaseCode d N).comp measurable_subtype_coe).subtype_mk

end CircleDomainRigidity

end

end OAI
