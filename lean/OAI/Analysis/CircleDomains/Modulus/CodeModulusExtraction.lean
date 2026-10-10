import OAI.Analysis.CircleDomains.Probability.PublishedMeasureDuality
import OAI.Analysis.CircleDomains.Probability.ConstrainedCodeLaws
import OAI.Analysis.CircleDomains.Modulus.RetaggedCost
import OAI.Analysis.CircleDomains.Probability.CountableVisitNorm
import OAI.Analysis.CircleDomains.Selection.CodeBarycenterDensities
import OAI.Analysis.CircleDomains.Selection.FreeLevelSections

namespace OAI

/-! Measure-family duality and probability lifting produce a law on the
constrained codes from a positive modulus bound. -/

open Set MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

omit [BorelSpace X] [BorelSpace D] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D] in
theorem costAdmissible_iff_constrained (d : PathCodeData X Y)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X)
    (h : PathCostSpace Y D → ℝ≥0∞) :
    CostAdmissible d p c ν h ↔
      ∀ Γ : ConstrainedCostCode d p c ν,
        1 ≤ ∫⁻ z, h z ∂(constrainedCodeMeasure d p c ν Γ : Measure (PathCostSpace Y D)) := by
  constructor
  · intro hadm Γ
    exact hadm Γ.val.val Γ.val.property Γ.property
  · intro hadm Γ hfinite hres
    exact hadm ⟨⟨Γ, hfinite⟩, hres⟩

variable [PolishSpace Y] [PolishSpace D]

theorem positive_modulus_code_law (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (p : D → X) (c : D → ℝ≥0∞) (ν : Measure X) [SFinite ν]
    [StandardBorelSpace (ConstrainedCostCode d p c ν)]
    (μ : Measure Y) [IsFiniteMeasure μ] (τ : Measure LevelTuple) [IsFiniteMeasure τ]
    (hc : (∑' s, c s ^ 2) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (r : ℝ≥0) (hr : 0 < r)
    (hmod : (r : ℝ≥0∞) < measureFamilyModulus (ConstrainedCostCode d p c ν)
      (PathCostSpace Y D) (pathCostReference μ c τ) (constrainedCodeMeasure d p c ν)) :
    ∃ (P : ProbabilityMeasure (BasePathCode d)) (q : PathCostSpace Y D → ℝ≥0∞),
      Measurable q ∧
      meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q ∧
      (∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), pathCostMeasure d p c Γ univ < ∞) ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  let : IsFiniteMeasure (pathCostReference μ c τ) := finite_pathCostReference μ c hc τ
  obtain ⟨P, q, hq, hbar, he⟩ := indexed_measure_duality _ _ hdual hlift
    (constrainedCodeMeasure d p c ν) (measurable_constrainedCodeMeasure d p c ν hU)
    (pathCostReference μ c τ) r hr hmod
  refine ⟨constrainedCodeLaw d p c ν P, q, hq, ?_, he,
    constrainedCodeLaw_finite d hU p c ν P, constrainedCodeLaw_residual_null d p c ν hB P⟩
  ext E hE
  rw [mean_constrainedCodeLaw d hU p c ν P hE]
  exact hbar E hE

end CircleDomainRigidity

end

end OAI
