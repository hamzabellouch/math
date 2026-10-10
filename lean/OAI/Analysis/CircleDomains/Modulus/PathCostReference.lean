import OAI.Analysis.CircleDomains.Probability.PathCostMeasure
import OAI.Analysis.CircleDomains.Selection.TupleReference

namespace OAI

/-! The finite reference measure for modulus: physical area, squared
countable-point weights, and the weighted tuple tori. Its square integral
is exactly the sum of the three corresponding energies. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

def atomicReference (c : D → ℝ≥0∞) : Measure D :=
  Measure.sum (fun s => (c s) ^ 2 • Measure.dirac s)

omit [TopologicalSpace D] [BorelSpace D] in
theorem atomicReference_univ (c : D → ℝ≥0∞) :
    atomicReference c univ = ∑' s, (c s) ^ 2 := by
  simp only [atomicReference, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]

omit [TopologicalSpace D] [BorelSpace D] in
theorem lintegral_atomicReference (c : D → ℝ≥0∞) (f : D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f s ∂atomicReference c = ∑' s, (c s) ^ 2 * f s := by
  rw [atomicReference, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

def pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞) (τ : Measure LevelTuple) :
    Measure (PathCostSpace Y D) :=
  μ.map costPhysical + (atomicReference c).map costAtomic + τ.map costTuple

theorem pathCostReference_univ (μ : Measure Y) (c : D → ℝ≥0∞) (τ : Measure LevelTuple) :
    pathCostReference μ c τ univ = μ univ + (∑' s, (c s) ^ 2) + τ univ := by
  simp only [pathCostReference, Measure.add_apply,
    Measure.map_apply measurable_costPhysical MeasurableSet.univ,
    Measure.map_apply measurable_costAtomic MeasurableSet.univ,
    Measure.map_apply measurable_costTuple MeasurableSet.univ,
    preimage_univ, atomicReference_univ]

theorem finite_pathCostReference (μ : Measure Y) [IsFiniteMeasure μ]
    (c : D → ℝ≥0∞) (hc : (∑' s, (c s) ^ 2) < ∞)
    (τ : Measure LevelTuple) [IsFiniteMeasure τ] : IsFiniteMeasure (pathCostReference μ c τ) := by
  constructor
  rw [pathCostReference_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ, hc⟩,
    measure_lt_top τ univ⟩

theorem lintegral_pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ∂pathCostReference μ c τ =
      (∫⁻ y, h (costPhysical y) ∂μ) +
      (∑' s, (c s) ^ 2 * h (costAtomic s)) + ∫⁻ t, h (costTuple t) ∂τ := by
  rw [pathCostReference, lintegral_add_measure, lintegral_add_measure,
    lintegral_map hh measurable_costPhysical, lintegral_map hh measurable_costAtomic,
    lintegral_map hh measurable_costTuple]
  rw [lintegral_atomicReference c (fun s => h (costAtomic s)) (hh.comp measurable_costAtomic)]

theorem squareIntegral_pathCostReference (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z ^ 2 ∂pathCostReference μ c τ =
      (∫⁻ y, h (costPhysical y) ^ 2 ∂μ) +
      (∑' s, (c s * h (costAtomic s)) ^ 2) + ∫⁻ t, h (costTuple t) ^ 2 ∂τ := by
  rw [lintegral_pathCostReference μ c τ _ (hh.pow_const 2)]
  simp only [mul_pow]

theorem null_tupleExclusions_of_reference_energy (μ : Measure Y) (c : D → ℝ≥0∞)
    (ω : TupleType → ℝ≥0∞) (hω : ∀ i, ω i ≠ 0)
    (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hint : (∫⁻ z, h z ^ 2 ∂pathCostReference μ c (tupleReference ω)) < ∞)
    (n : ℕ) (l : Fin (n + 1) → ℕ) :
    volume (tupleInfiniteExclusions (h ∘ costTuple) n l) = 0 := by
  apply null_tupleInfiniteExclusions hω (hh.comp measurable_costTuple)
  rw [squareIntegral_pathCostReference μ c (tupleReference ω) h hh] at hint
  exact lt_of_le_of_lt le_add_self hint

end CircleDomainRigidity

end

end OAI
