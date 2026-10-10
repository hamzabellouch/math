import OAI.Analysis.CircleDomains.Modulus.ConstrainedCostCodes
import OAI.Analysis.CircleDomains.Probability.CodeLawMeasures

namespace OAI

/-! Forgetting the constrained finite-code subtype produces an actual law
on base paths, retaining the residual nullity and finite-cost properties. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

def constrainedCodeToBase (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (Γ : ConstrainedCostCode d p c ν) : BasePathCode d := Γ.val.val

omit [BorelSpace X] [BorelSpace D] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D] in
theorem measurable_constrainedCodeToBase (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) :
    Measurable (constrainedCodeToBase d p c ν) :=
  measurable_subtype_coe.comp measurable_subtype_coe

def constrainedCodeLaw (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) :
    ProbabilityMeasure (BasePathCode d) := P.map (constrainedCodeToBase d p c ν)

omit [BorelSpace D] [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [Countable D] in
theorem constrainedCodeLaw_residual_null (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν]
    (hB : IsClosed d.dust) (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) :
    ∀ᵐ Γ ∂(constrainedCodeLaw d p c ν P : Measure (BasePathCode d)),
      ν (residualImage d.dust Γ.val) = 0 := by
  apply (ae_map_iff (measurable_constrainedCodeToBase d p c ν).aemeasurable
    ((measurableSet_residualImageMass_zero hB ν).preimage measurable_subtype_coe)).mpr
  exact Eventually.of_forall fun Γ => Γ.property

theorem constrainedCodeLaw_finite (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) :
    ∀ᵐ Γ ∂(constrainedCodeLaw d p c ν P : Measure (BasePathCode d)),
      pathCostMeasure d p c Γ univ < ∞ := by
  apply (ae_map_iff (measurable_constrainedCodeToBase d p c ν).aemeasurable
    (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp
      (measurable_pathCostMeasure d hU p c)) measurable_const)).mpr
  exact Eventually.of_forall fun Γ => Γ.val.property

theorem mean_constrainedCodeLaw (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (P : ProbabilityMeasure (ConstrainedCostCode d p c ν)) {A : Set (PathCostSpace Y D)}
    (hA : MeasurableSet A) :
    meanCodeCost d p c (constrainedCodeLaw d p c ν P) A =
      ∫⁻ Γ, (constrainedCodeMeasure d p c ν Γ : Measure (PathCostSpace Y D)) A
        ∂(P : Measure (ConstrainedCostCode d p c ν)) := by
  rw [meanCodeCost_apply d hU p c _ hA]
  exact lintegral_map ((Measure.measurable_coe hA).comp
    (measurable_pathCostMeasure d hU p c)) (measurable_constrainedCodeToBase d p c ν)

end CircleDomainRigidity

end

end OAI
