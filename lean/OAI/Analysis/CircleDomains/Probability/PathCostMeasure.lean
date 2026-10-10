import OAI.Analysis.CircleDomains.Topology.BasePathCodes
import OAI.Analysis.CircleDomains.Probability.AtomicVisitMeasure
import OAI.Analysis.CircleDomains.Probability.TagTupleMeasure

namespace OAI

/-! The actual three-part coding measure: physical occupation, countable
preterminal visits, and weighted tuples. Finiteness is a Borel code condition. -/

open Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

def PathCostSpace (Y D : Type*) := Y ⊕ (D ⊕ LevelTuple)

instance {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D] :
    TopologicalSpace (PathCostSpace Y D) := inferInstanceAs (TopologicalSpace (Y ⊕ (D ⊕ LevelTuple)))
instance {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D] :
    MeasurableSpace (PathCostSpace Y D) := borel (PathCostSpace Y D)
instance {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D] :
    BorelSpace (PathCostSpace Y D) := ⟨rfl⟩
instance {Y D : Type*} [TopologicalSpace Y] [TopologicalSpace D]
    [PolishSpace Y] [PolishSpace D] : PolishSpace (PathCostSpace Y D) :=
  inferInstanceAs (PolishSpace (Y ⊕ (D ⊕ LevelTuple)))

def costPhysical {Y D : Type*} : Y → PathCostSpace Y D := Sum.inl

def costAtomic {Y D : Type*} : D → PathCostSpace Y D := Sum.inr ∘ Sum.inl

def costTuple {Y D : Type*} : LevelTuple → PathCostSpace Y D := Sum.inr ∘ Sum.inr

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

omit [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costPhysical : Measurable (costPhysical (Y := Y) (D := D)) := by
  have hc : Continuous (costPhysical (Y := Y) (D := D)) := continuous_inl
  exact Continuous.measurable (α := Y) (γ := PathCostSpace Y D) hc

omit [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costAtomic : Measurable (costAtomic (Y := Y) (D := D)) := by
  have hc : Continuous (costAtomic (Y := Y) (D := D)) := continuous_inr.comp continuous_inl
  exact Continuous.measurable (α := D) (γ := PathCostSpace Y D) hc

omit [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_costTuple : Measurable (costTuple (Y := Y) (D := D)) := by
  have hc : Continuous (costTuple (Y := Y) (D := D)) := continuous_inr.comp continuous_inr
  exact Continuous.measurable (α := LevelTuple) (γ := PathCostSpace Y D) hc

def baseCodeOccupation (d : PathCodeData X Y) (Γ : BasePathCode d) : Measure Y :=
  dyadicPhysicalOccupation d.domainEquiv d.basePoint (baseCodePhysicalPath d Γ)

def pathCostMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) : Measure (PathCostSpace Y D) :=
  (baseCodeOccupation d Γ).map costPhysical +
  (atomicVisitMeasure p c Γ.val.1).map costAtomic +
  (weightedTupleMeasure Γ.val.2).map costTuple

instance (d : PathCodeData X Y) (Γ : BasePathCode d) : IsFiniteMeasure (baseCodeOccupation d Γ) := by
  unfold baseCodeOccupation
  infer_instance

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem baseCodeOccupation_univ (d : PathCodeData X Y) (Γ : BasePathCode d) :
    baseCodeOccupation d Γ univ = physicalDomainLength d.domainEquiv d.basePoint Γ.val.1 :=
  dyadicPhysicalOccupation_univ _ _ _

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem pathCostMeasure_univ (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) :
    pathCostMeasure d p c Γ univ =
      physicalDomainLength d.domainEquiv d.basePoint Γ.val.1 +
      (∑' s, c s * preterminalVisitCount Γ.val.1 (p s)) + weightedTupleMeasure Γ.val.2 univ := by
  simp only [pathCostMeasure, Measure.add_apply,
    Measure.map_apply measurable_costPhysical MeasurableSet.univ,
    Measure.map_apply measurable_costAtomic MeasurableSet.univ,
    Measure.map_apply measurable_costTuple MeasurableSet.univ,
    preimage_univ, baseCodeOccupation_univ, atomicVisitMeasure_univ]

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem pathCostMeasure_finite_iff (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) :
    pathCostMeasure d p c Γ univ < ∞ ↔
      (∑' s, c s * preterminalVisitCount Γ.val.1 (p s)) < ∞ := by
  rw [pathCostMeasure_univ]
  have hp := Γ.property.1.1
  have ht := measure_lt_top (weightedTupleMeasure Γ.val.2) univ
  simp only [ENNReal.add_lt_top, hp, ht, true_and, and_true]

variable [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [SecondCountableTopology X] in
theorem measurable_baseCodeOccupation (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) :
    Measurable (baseCodeOccupation d) :=
  (measurable_dyadicPhysicalOccupation d.domainEquiv hU d.basePoint).comp
    ((measurable_fst.comp measurable_subtype_coe).subtype_mk)

theorem measurable_pathCostMeasure (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) : Measurable (pathCostMeasure d p c) := by
  exact (((Measure.measurable_map _ measurable_costPhysical).comp
    (measurable_baseCodeOccupation d hU)).add
    ((Measure.measurable_map _ measurable_costAtomic).comp
      ((measurable_atomicVisitMeasure p c).comp (measurable_fst.comp measurable_subtype_coe)))).add
    ((Measure.measurable_map _ measurable_costTuple).comp
      (measurable_weightedTupleMeasure.comp (measurable_snd.comp measurable_subtype_coe)))

abbrev FiniteCostCode (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞) :=
  {Γ : BasePathCode d // pathCostMeasure d p c Γ univ < ∞}

theorem measurableSet_finiteCostCode (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) :
    MeasurableSet {Γ : BasePathCode d | pathCostMeasure d p c Γ univ < ∞} :=
  measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_pathCostMeasure d hU p c)) measurable_const

theorem standardBorel_finiteCostCode (d : PathCodeData X Y) [StandardBorelSpace (BasePathCode d)]
    (hU : IsOpen d.quotientDomain) (p : D → X) (c : D → ℝ≥0∞) :
    StandardBorelSpace (FiniteCostCode d p c) :=
  (measurableSet_finiteCostCode d hU p c).standardBorel

instance (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞) (Γ : FiniteCostCode d p c) :
    IsFiniteMeasure (pathCostMeasure d p c Γ.val) := ⟨Γ.property⟩

omit [BorelSpace X] [BorelSpace C(PathTime, X)]
  [SecondCountableTopology X] [Countable D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem lintegral_pathCostMeasure (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (Γ : BasePathCode d) (f : PathCostSpace Y D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂pathCostMeasure d p c Γ =
      (∫⁻ y, f (costPhysical y) ∂baseCodeOccupation d Γ) +
      (∑' s, (c s * preterminalVisitCount Γ.val.1 (p s)) * f (costAtomic s)) +
      ∫⁻ t, f (costTuple t) ∂weightedTupleMeasure Γ.val.2 := by
  rw [pathCostMeasure, lintegral_add_measure, lintegral_add_measure,
    lintegral_map hf measurable_costPhysical, lintegral_map hf measurable_costAtomic,
    lintegral_map hf measurable_costTuple]
  rw [lintegral_atomicVisitMeasure p c Γ.val.1 (fun s => f (costAtomic s))
    (hf.comp measurable_costAtomic)]

end CircleDomainRigidity

end

end OAI
