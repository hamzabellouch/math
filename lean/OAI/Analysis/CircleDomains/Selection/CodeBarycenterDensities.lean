import OAI.Analysis.CircleDomains.Probability.CodeLawAbsoluteContinuity

namespace OAI

/-! The three components of a coding barycenter have the restrictions
of its density. Their square energies are bounded by the total energy. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

private theorem withDensity_map_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) {f : A → B} (hf : Measurable f) {q : B → ℝ≥0∞} (hq : Measurable q) :
    (μ.map f).withDensity q = (μ.withDensity (q ∘ f)).map f := by
  ext E hE
  rw [withDensity_apply q hE, Measure.restrict_map hf hE,
    lintegral_map hq hf, Measure.map_apply hf hE,
    withDensity_apply (q ∘ f) (hf hE)]
  rfl

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

theorem withDensity_sumCostMeasures (μ : Measure Y) (a : Measure D) (τ : Measure LevelTuple)
    (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q) :
    (sumCostMeasures μ a τ).withDensity q =
      sumCostMeasures (μ.withDensity (q ∘ costPhysical))
        (a.withDensity (q ∘ costAtomic)) (τ.withDensity (q ∘ costTuple)) := by
  simp only [sumCostMeasures, withDensity_add_measure,
    withDensity_map_comp _ measurable_costPhysical hq,
    withDensity_map_comp _ measurable_costAtomic hq,
    withDensity_map_comp _ measurable_costTuple hq]

theorem sumCostMeasures_injective {μ μ' : Measure Y} {a a' : Measure D}
    {τ τ' : Measure LevelTuple} (h : sumCostMeasures μ a τ = sumCostMeasures μ' a' τ') :
    μ = μ' ∧ a = a' ∧ τ = τ' := by
  refine ⟨?_, ?_, ?_⟩
  · ext E hE
    have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costPhysical '' E)) h
    simpa only [sumCostMeasures_physical _ _ _ hE] using he
  · ext E hE
    have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costAtomic '' E)) h
    simpa only [sumCostMeasures_atomic _ _ _ hE] using he
  · ext E hE
    have he := congrArg (fun ν : Measure (PathCostSpace Y D) => ν (costTuple '' E)) h
    simpa only [sumCostMeasures_tuple _ _ _ hE] using he

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D]

theorem codeLaw_component_densities (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (p : D → X) (c : D → ℝ≥0∞) (P : ProbabilityMeasure (BasePathCode d))
    (μ : Measure Y) (τ : Measure LevelTuple) (q : PathCostSpace Y D → ℝ≥0∞)
    (hq : Measurable q)
    (hbar : meanCodeCost d p c P = (pathCostReference μ c τ).withDensity q) :
    meanCodeOccupation d P = μ.withDensity (q ∘ costPhysical) ∧
      meanCodeAtomic d p c P = (atomicReference c).withDensity (q ∘ costAtomic) ∧
      meanCodeTuple d P = τ.withDensity (q ∘ costTuple) := by
  rw [meanCodeCost_eq d hU p c P] at hbar
  change sumCostMeasures (meanCodeOccupation d P) (meanCodeAtomic d p c P)
    (meanCodeTuple d P) = (sumCostMeasures μ (atomicReference c) τ).withDensity q at hbar
  rw [withDensity_sumCostMeasures μ (atomicReference c) τ q hq] at hbar
  exact sumCostMeasures_injective hbar

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)]
  [BorelSpace C(PathTime, X)] [MeasurableSpace C(PathTime, Y)]
  [BorelSpace C(PathTime, Y)] [SecondCountableTopology X] [Countable D] in
theorem codeReference_component_energies (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (q : PathCostSpace Y D → ℝ≥0∞) (hq : Measurable q) :
    (∫⁻ y, q (costPhysical y) ^ 2 ∂μ) ≤ ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ ∧
      (∫⁻ t, q (costTuple t) ^ 2 ∂τ) ≤ ∫⁻ z, q z ^ 2 ∂pathCostReference μ c τ := by
  rw [squareIntegral_pathCostReference μ c τ q hq]
  exact ⟨le_add_of_le_left le_self_add, le_add_self⟩

end CircleDomainRigidity

end

end OAI
