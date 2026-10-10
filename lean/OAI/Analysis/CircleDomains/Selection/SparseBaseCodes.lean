import OAI.Analysis.CircleDomains.Probability.PathCostMeasure
import OAI.Analysis.CircleDomains.Selection.SparseTags

namespace OAI

/-! Injective retagging preserves the complete base-code conditions and cost finiteness.
It is a Borel operation on the actual code space. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

theorem allowedTaggedPath_sparse (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (e : ℕ ↪ ℕ) {Γ : TaggedPath X} (hΓ : AllowedTaggedPath d ν T Γ) :
    AllowedTaggedPath d ν T (sparseTaggedPath e Γ) := by
  refine ⟨hΓ.1, tagRules_sparse d.levels T e hΓ.2.1, ?_, ?_, ?_⟩
  · exact (residualConstraintFamily_sparse _ _ _ _ _ e Γ).mpr hΓ.2.2.1
  · exact (residualConstraintFamily_sparse _ _ _ _ _ e Γ).mpr hΓ.2.2.2.1
  · rw [residualImage_sparse]
    exact hΓ.2.2.2.2

theorem endpointCode_sparse (d : PathCodeData X Y) (ν : Measure X)
    (T : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (e : ℕ ↪ ℕ) {Γ : TaggedPath X} (hΓ : EndpointCode d ν T Γ) :
    EndpointCode d ν T (sparseTaggedPath e Γ) :=
  ⟨allowedTaggedPath_sparse d ν T e hΓ.1, hΓ.2⟩

def sparseBaseCode (d : PathCodeData X Y) (e : ℕ ↪ ℕ) (Γ : BasePathCode d) : BasePathCode d :=
  ⟨sparseTaggedPath e Γ.val, endpointCode_sparse d 0 (fun _ _ => ∅) e Γ.property⟩

variable [BorelSpace C(PathTime, X)]

theorem measurable_sparseBaseCode (d : PathCodeData X Y) (e : ℕ ↪ ℕ) :
    Measurable (sparseBaseCode d e) :=
  (((continuous_sparseTaggedPath e).measurable).comp measurable_subtype_coe).subtype_mk

variable {D : Type*} [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]
  [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [BorelSpace C(PathTime, X)] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem baseCodeOccupation_sparse (d : PathCodeData X Y) (e : ℕ ↪ ℕ) (Γ : BasePathCode d) :
    baseCodeOccupation d (sparseBaseCode d e Γ) = baseCodeOccupation d Γ := rfl

omit [BorelSpace C(PathTime, X)] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem pathCostMeasure_sparse_finite_iff (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (e : ℕ ↪ ℕ) (Γ : BasePathCode d) :
    pathCostMeasure d p c (sparseBaseCode d e Γ) univ < ∞ ↔
      pathCostMeasure d p c Γ univ < ∞ := by
  rw [pathCostMeasure_finite_iff, pathCostMeasure_finite_iff]
  rfl

variable [SecondCountableTopology X] [Countable D]

def sparseFiniteCostCode (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (e : ℕ ↪ ℕ) (Γ : FiniteCostCode d p c) : FiniteCostCode d p c :=
  ⟨sparseBaseCode d e Γ.val, (pathCostMeasure_sparse_finite_iff d p c e Γ.val).mpr Γ.property⟩

omit [SecondCountableTopology X] [Countable D] [BorelSpace X]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_sparseFiniteCostCode (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (e : ℕ ↪ ℕ) :
    Measurable (sparseFiniteCostCode d p c e) :=
  ((measurable_sparseBaseCode d e).comp measurable_subtype_coe).subtype_mk

end CircleDomainRigidity

end

end OAI
