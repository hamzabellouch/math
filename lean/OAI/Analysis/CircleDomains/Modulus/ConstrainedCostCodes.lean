import OAI.Analysis.CircleDomains.Selection.SparseBaseCodes
import Mathlib.MeasureTheory.Measure.FiniteMeasure

namespace OAI

/-! The actual finite coding-measure family with a prescribed null
residual-image constraint, as a standard Borel space of codes. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

abbrev ConstrainedCostCode (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) :=
  {Γ : FiniteCostCode d p c // ν (residualImage d.dust Γ.val.val) = 0}

omit [BorelSpace D] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [Countable D] in
theorem measurableSet_constrainedCostCode (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν] (hB : IsClosed d.dust) :
    MeasurableSet {Γ : FiniteCostCode d p c | ν (residualImage d.dust Γ.val.val) = 0} :=
  (measurableSet_residualImageMass_zero hB ν).preimage
    (measurable_subtype_coe.comp measurable_subtype_coe)

omit [BorelSpace D] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [Countable D] in
theorem standardBorel_constrainedCostCode (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν] (hB : IsClosed d.dust)
    [StandardBorelSpace (FiniteCostCode d p c)] :
    StandardBorelSpace (ConstrainedCostCode d p c ν) :=
  (measurableSet_constrainedCostCode d p c ν hB).standardBorel

def finiteCodeMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : FiniteCostCode d p c) : FiniteMeasure (PathCostSpace Y D) :=
  ⟨pathCostMeasure d p c Γ.val, inferInstance⟩

theorem measurable_finiteCodeMeasure (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (hU : IsOpen d.quotientDomain) :
    Measurable (finiteCodeMeasure d p c) :=
  ((measurable_pathCostMeasure d hU p c).comp measurable_subtype_coe).subtype_mk

def constrainedCodeMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (Γ : ConstrainedCostCode d p c ν) : FiniteMeasure (PathCostSpace Y D) :=
  finiteCodeMeasure d p c Γ.val

theorem measurable_constrainedCodeMeasure (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) (hU : IsOpen d.quotientDomain) :
    Measurable (constrainedCodeMeasure d p c ν) :=
  (measurable_finiteCodeMeasure d p c hU).comp measurable_subtype_coe

def sparseConstrainedCostCode (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (e : ℕ ↪ ℕ) (Γ : ConstrainedCostCode d p c ν) :
    ConstrainedCostCode d p c ν :=
  ⟨sparseFiniteCostCode d p c e Γ.val, by
    change ν (residualImage d.dust (sparseTaggedPath e Γ.val.val.val)) = 0
    rw [residualImage_sparse]
    exact Γ.property⟩

omit [BorelSpace X] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D] in
theorem measurable_sparseConstrainedCostCode (d : PathCodeData X Y) (p : D → X)
    (c : D → ℝ≥0∞) (ν : Measure X) (e : ℕ ↪ ℕ) :
    Measurable (sparseConstrainedCostCode d p c ν e) :=
  ((measurable_sparseFiniteCostCode d p c e).comp measurable_subtype_coe).subtype_mk

end CircleDomainRigidity

end

end OAI
