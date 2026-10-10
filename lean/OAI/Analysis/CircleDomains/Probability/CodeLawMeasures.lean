import OAI.Analysis.CircleDomains.Probability.PathCostMeasure

namespace OAI

/-! Actual mean occupation, atomic and tuple measures of a law on base
codes. Their sum is exactly the barycenter of the coding measures. -/

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

omit [TopologicalSpace D] [MeasurableSpace Y] [BorelSpace Y] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem measurable_baseCodeAtomic (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞) :
    Measurable (fun Γ : BasePathCode d => atomicVisitMeasure p c Γ.val.1) :=
  (measurable_atomicVisitMeasure p c).comp (measurable_fst.comp measurable_subtype_coe)

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] in
theorem measurable_baseCodeTuple (d : PathCodeData X Y) :
    Measurable (fun Γ : BasePathCode d => weightedTupleMeasure Γ.val.2) :=
  measurable_weightedTupleMeasure.comp (measurable_snd.comp measurable_subtype_coe)

def meanCodeOccupation (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) : Measure Y :=
  (P : Measure (BasePathCode d)).bind (baseCodeOccupation d)

def meanCodeAtomic (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) : Measure D :=
  (P : Measure (BasePathCode d)).bind (fun Γ => atomicVisitMeasure p c Γ.val.1)

def meanCodeTuple (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) :
    Measure LevelTuple :=
  (P : Measure (BasePathCode d)).bind (fun Γ => weightedTupleMeasure Γ.val.2)

def meanCodeCost (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) : Measure (PathCostSpace Y D) :=
  (P : Measure (BasePathCode d)).bind (pathCostMeasure d p c)

omit [BorelSpace X] [SecondCountableTopology X] in
theorem meanCodeOccupation_apply (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (P : ProbabilityMeasure (BasePathCode d)) {A : Set Y} (hA : MeasurableSet A) :
    meanCodeOccupation d P A = ∫⁻ Γ, baseCodeOccupation d Γ A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeOccupation d hU).aemeasurable

omit [TopologicalSpace D] [MeasurableSpace Y] [BorelSpace Y] [BorelSpace D]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanCodeAtomic_apply (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) {A : Set D} (hA : MeasurableSet A) :
    meanCodeAtomic d p c P A = ∫⁻ Γ, atomicVisitMeasure p c Γ.val.1 A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeAtomic d p c).aemeasurable

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] in
theorem meanCodeTuple_apply (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    {A : Set LevelTuple} (hA : MeasurableSet A) :
    meanCodeTuple d P A = ∫⁻ Γ, weightedTupleMeasure Γ.val.2 A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_baseCodeTuple d).aemeasurable

theorem meanCodeCost_apply (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d))
    {A : Set (PathCostSpace Y D)} (hA : MeasurableSet A) :
    meanCodeCost d p c P A = ∫⁻ Γ, pathCostMeasure d p c Γ A ∂(P : Measure (BasePathCode d)) :=
  Measure.bind_apply hA (measurable_pathCostMeasure d hU p c).aemeasurable

theorem meanCodeCost_eq (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d)) :
    meanCodeCost d p c P =
      (meanCodeOccupation d P).map costPhysical +
      (meanCodeAtomic d p c P).map costAtomic + (meanCodeTuple d P).map costTuple := by
  ext A hA
  rw [meanCodeCost_apply d hU p c P hA, Measure.add_apply, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hA, Measure.map_apply measurable_costAtomic hA,
    Measure.map_apply measurable_costTuple hA,
    meanCodeOccupation_apply d hU P (measurable_costPhysical hA),
    meanCodeAtomic_apply d p c P (measurable_costAtomic hA),
    meanCodeTuple_apply d P (measurable_costTuple hA)]
  simp_rw [pathCostMeasure, Measure.add_apply,
    Measure.map_apply measurable_costPhysical hA, Measure.map_apply measurable_costAtomic hA,
    Measure.map_apply measurable_costTuple hA]
  have hp : Measurable (fun Γ : BasePathCode d =>
      baseCodeOccupation d Γ (costPhysical ⁻¹' A)) :=
    (Measure.measurable_coe (measurable_costPhysical hA)).comp
    (measurable_baseCodeOccupation d hU)
  have ha : Measurable (fun Γ : BasePathCode d =>
      atomicVisitMeasure p c Γ.val.1 (costAtomic ⁻¹' A)) :=
    (Measure.measurable_coe (measurable_costAtomic hA)).comp
    (measurable_baseCodeAtomic d p c)
  have hpa : Measurable (fun Γ : BasePathCode d =>
      baseCodeOccupation d Γ (costPhysical ⁻¹' A) +
        atomicVisitMeasure p c Γ.val.1 (costAtomic ⁻¹' A)) := hp.add ha
  rw [lintegral_add_left hpa, lintegral_add_left hp]

end CircleDomainRigidity

end

end OAI
