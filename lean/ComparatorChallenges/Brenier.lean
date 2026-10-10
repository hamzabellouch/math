import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

abbrev E (dimension : ℕ) := EuclideanSpace ℝ (Fin dimension)

def uniformMeasure {dimension : ℕ} (source : Set (E dimension)) : Measure (E dimension) :=
  (volume source)⁻¹ • volume.restrict source

def IsSupported {dimension : ℕ} (measure : Measure (E dimension))
    (container : Set (E dimension)) : Prop :=
  measure (containerᶜ) = 0

def IsCoupling {dimension : ℕ} (source target : Measure (E dimension))
    (plan : Measure (E dimension × E dimension)) : Prop :=
  IsProbabilityMeasure plan ∧
    Measure.map Prod.fst plan = source ∧
    Measure.map Prod.snd plan = target

def quadraticPlanCost {dimension : ℕ} (plan : Measure (E dimension × E dimension)) :
    ℝ≥0∞ :=
  ∫⁻ pair, ENNReal.ofReal (‖pair.1 - pair.2‖ ^ 2) ∂plan

def wasserstein2 {dimension : ℕ} (source target : Measure (E dimension)) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (sInf {cost : ℝ≥0∞ |
        ∃ plan : Measure (E dimension × E dimension),
          IsCoupling source target plan ∧ quadraticPlanCost plan = cost}))

def graphPlan {dimension : ℕ} (source : Measure (E dimension))
    (transport : E dimension → E dimension) : Measure (E dimension × E dimension) :=
  Measure.map (fun point => (point, transport point)) source

def IsQuadraticOptimalMap {dimension : ℕ} (source target : Measure (E dimension))
    (transport : E dimension → E dimension) : Prop :=
  Measurable transport ∧
    Measure.map transport source = target ∧
    ∀ plan : Measure (E dimension × E dimension),
      IsCoupling source target plan →
        quadraticPlanCost (graphPlan source transport) ≤ quadraticPlanCost plan

def IsUniqueQuadraticOptimalMap {dimension : ℕ} (source target : Measure (E dimension))
    (transport : E dimension → E dimension) : Prop :=
  IsQuadraticOptimalMap source target transport ∧
    ∀ plan : Measure (E dimension × E dimension),
      IsCoupling source target plan →
        quadraticPlanCost plan ≤ quadraticPlanCost (graphPlan source transport) →
          plan = graphPlan source transport

def mapL2Dist {dimension : ℕ} (source : Measure (E dimension))
    (first second : E dimension → E dimension) : ℝ :=
  Real.sqrt (∫ point, ‖first point - second point‖ ^ 2 ∂source)

def cube (dimension : ℕ) : Set (E dimension) :=
  {point | ∀ index, |point index| ≤ 1}

def HasExactlyThreeAtoms {dimension : ℕ} (measure : Measure (E dimension))
    (container : Set (E dimension)) : Prop :=
  ∃ atoms : Fin 3 → E dimension, Function.Injective atoms ∧
    (∀ index, atoms index ∈ container) ∧
    ∃ weights : Fin 3 → ℝ≥0∞, (∀ index, 0 < weights index) ∧
      (∑ index, weights index) = 1 ∧
      measure = ∑ index, weights index • Measure.dirac (atoms index)

theorem one_third_stability :
    ∀ (dimension : ℕ) (source container : Set (E dimension)),
      2 ≤ dimension → IsCompact source → Convex ℝ source → (interior source).Nonempty →
      IsCompact container → container.Nonempty →
      ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (first second : Measure (E dimension)),
          IsProbabilityMeasure first → IsProbabilityMeasure second →
          IsSupported first container → IsSupported second container →
          ∃ firstMap secondMap : E dimension → E dimension,
            IsUniqueQuadraticOptimalMap (uniformMeasure source) first firstMap ∧
            IsUniqueQuadraticOptimalMap (uniformMeasure source) second secondMap ∧
            mapL2Dist (uniformMeasure source) firstMap secondMap ≤
              constant * Real.rpow (wasserstein2 first second) (1 / 3 : ℝ) := by
  sorry

theorem one_third_exponent_is_sharp :
    ∀ (dimension : ℕ), 2 ≤ dimension → ∀ exponent : ℝ, (1 / 3 : ℝ) < exponent →
      ∀ constant : ℝ, 0 < constant →
        ∃ (first second : Measure (E dimension)) (firstMap secondMap : E dimension → E dimension),
          IsProbabilityMeasure first ∧ IsProbabilityMeasure second ∧
          IsSupported first (cube dimension) ∧ IsSupported second (cube dimension) ∧
          HasExactlyThreeAtoms first (cube dimension) ∧
          HasExactlyThreeAtoms second (cube dimension) ∧
          first ≠ second ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) first firstMap ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) second secondMap ∧
          0 < wasserstein2 first second ∧
          constant * Real.rpow (wasserstein2 first second) exponent <
            mapL2Dist (uniformMeasure (cube dimension)) firstMap secondMap := by
  sorry

end Problem358

end

end OAI
