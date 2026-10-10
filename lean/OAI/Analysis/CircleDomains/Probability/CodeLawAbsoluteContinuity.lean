import OAI.Analysis.CircleDomains.Modulus.CostSummands
import OAI.Analysis.CircleDomains.Probability.CodeHitMeasures

namespace OAI

/-! A density for the total coding barycenter gives absolute continuity
on each cost summand, including every tuple slot and the whole-image
atomless tests. -/

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

theorem codeLaw_components_absolutelyContinuous (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    meanCodeOccupation d P ≪ μ ∧ meanCodeAtomic d p c P ≪ atomicReference c ∧
      meanCodeTuple d P ≪ τ := by
  have hac := withDensity_absolutelyContinuous (pathCostReference μ c τ) q
  rw [← hbar, meanCodeCost_eq d hU p c P] at hac
  exact sumCostMeasures_absolutelyContinuous hac

theorem codeLaw_slot_absolutelyContinuous (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) (k : ℕ) :
    slotLaw d P k ≪ τ :=
  slotLaw_absolutelyContinuous d P τ
    (codeLaw_components_absolutelyContinuous d hU p c P μ τ q hbar).2.2 k

theorem codeLaw_whole_image_test (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (ω : TupleType → ℝ≥0∞)
    (q : PathCostSpace Y D → ℝ≥0∞)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c (tupleReference ω)).withDensity q)
    (ν : Measure X) [SFinite ν]
    (hfree : ∀ᵐ x ∂ν, x ∈ d.dust ∧
      ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0)
    (hres : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) :
    ∫⁻ x, codeHitProbability d P x ∂ν = 0 :=
  lintegral_codeHitProbability_zero d hB hH P ω
    (codeLaw_components_absolutelyContinuous d hU p c P μ (tupleReference ω) q hbar).2.2
    ν hfree hres

end CircleDomainRigidity

end

end OAI
