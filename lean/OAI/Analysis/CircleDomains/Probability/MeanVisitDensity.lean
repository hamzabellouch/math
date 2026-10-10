import OAI.Analysis.CircleDomains.Modulus.CostSummands
import OAI.Analysis.CircleDomains.Probability.CodeLawMeasures

namespace OAI

/-! The density on a countable cost atom records the actual mean number
of preterminal visits. The squared density budget therefore bounds the
counting square norm independently of the auxiliary positive weights. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSingletonClass D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

def meanCodePreVisits (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (x : X) : ℝ≥0∞ :=
  ∫⁻ Γ : BasePathCode d, preterminalVisitCount Γ.val.1 x ∂(P : Measure (BasePathCode d))

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)]
  [BorelSpace C(PathTime, X)] [SecondCountableTopology X] [TopologicalSpace D]
  [BorelSpace D] [Countable D] in
theorem atomicVisitMeasure_singleton (p : D → X) (c : D → ℝ≥0∞)
    (γ : C(PathTime, X)) (s : D) :
    atomicVisitMeasure p c γ {s} = c s * preterminalVisitCount γ (p s) := by
  classical
  rw [atomicVisitMeasure_apply p c γ (measurableSet_singleton s)]
  simp [Set.indicator]

omit [TopologicalSpace D] [BorelSpace D] [Countable D] in
theorem atomicReference_singleton (c : D → ℝ≥0∞) (s : D) :
    atomicReference c {s} = (c s) ^ 2 := by
  classical
  simp only [atomicReference, Measure.sum_apply _ (measurableSet_singleton s),
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton s)]
  simp [Set.indicator]

omit [TopologicalSpace D] [BorelSpace D] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem meanCodeAtomic_singleton (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (P : ProbabilityMeasure (BasePathCode d)) (s : D) :
    meanCodeAtomic d p c P {s} = c s * meanCodePreVisits d P (p s) := by
  rw [meanCodeAtomic_apply d p c P (measurableSet_singleton s)]
  simp_rw [atomicVisitMeasure_singleton]
  exact lintegral_const_mul _ (measurable_preterminalVisitCount.comp
    ((measurable_fst.comp measurable_subtype_coe).prodMk measurable_const))

theorem meanCodePreVisits_density (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d))
    (μ : Measure Y) (τ : Measure LevelTuple) (q : PathCostSpace Y D → ℝ≥0∞)
    (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q)
    (s : D) (hc0 : c s ≠ 0) (hct : c s ≠ ∞) :
    meanCodePreVisits d P (p s) = c s * q (costAtomic s) := by
  have hA := measurableSet_singleton s
  have hI := (measurableEmbedding_costAtomic (Y := Y) (D := D)).measurableSet_image.mpr hA
  have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costAtomic '' {s})) hbar
  rw [meanCodeCost_eq d hU p c P] at he
  change sumCostMeasures (meanCodeOccupation d P) (meanCodeAtomic d p c P)
    (meanCodeTuple d P) (costAtomic '' {s}) = _ at he
  rw [sumCostMeasures_atomic _ _ _ hA, meanCodeAtomic_singleton,
    withDensity_apply q hI, Set.image_singleton, lintegral_singleton' hq] at he
  have href : pathCostReference μ c τ {costAtomic s} = (c s) ^ 2 := by
    rw [← Set.image_singleton]
    exact (sumCostMeasures_atomic μ (atomicReference c) τ hA).trans
      (atomicReference_singleton c s)
  rw [href] at he
  apply (ENNReal.mul_left_inj hc0 hct).mp
  calc
    meanCodePreVisits d P (p s) * c s = c s * meanCodePreVisits d P (p s) := mul_comm _ _
    _ = q (costAtomic s) * (c s) ^ 2 := he
    _ = (c s * q (costAtomic s)) * c s := by rw [pow_two]; ac_rfl

theorem meanCodePreVisits_square_budget (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (hc0 : ∀ s, c s ≠ 0) (hct : ∀ s, c s ≠ ∞)
    (P : ProbabilityMeasure (BasePathCode d)) (μ : Measure Y) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    (∑' s, meanCodePreVisits d P (p s) ^ 2) ≤
      ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ := by
  simp_rw [meanCodePreVisits_density d hU p c P μ τ q hq hbar _ (hc0 _) (hct _)]
  rw [squareIntegral_pathCostReference μ c τ q hq]
  exact le_trans le_add_self le_self_add

end CircleDomainRigidity

end

end OAI
