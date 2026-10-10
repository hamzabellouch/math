import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def uniformMeasure {d : ℕ} (K : Set (E d)) : Measure (E d) :=
  (volume K)⁻¹ • volume.restrict K

def IsSupported {d : ℕ} (μ : Measure (E d)) (Y : Set (E d)) : Prop :=
  μ (Yᶜ) = 0

def IsCoupling {d : ℕ} (μ ν : Measure (E d))
    (π : Measure (E d × E d)) : Prop :=
  IsProbabilityMeasure π ∧
    Measure.map Prod.fst π = μ ∧
    Measure.map Prod.snd π = ν

def quadraticPlanCost {d : ℕ} (π : Measure (E d × E d)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π

def wasserstein2 {d : ℕ} (μ ν : Measure (E d)) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (sInf {r : ℝ≥0∞ |
        ∃ π : Measure (E d × E d),
          IsCoupling μ ν π ∧ quadraticPlanCost π = r}))

def graphPlan {d : ℕ} (ρ : Measure (E d)) (T : E d → E d) :
    Measure (E d × E d) :=
  Measure.map (fun x => (x, T x)) ρ

def IsQuadraticOptimalMap {d : ℕ} (ρ μ : Measure (E d))
    (T : E d → E d) : Prop :=
  Measurable T ∧
    Measure.map T ρ = μ ∧
    ∀ π : Measure (E d × E d),
      IsCoupling ρ μ π →
        quadraticPlanCost (graphPlan ρ T) ≤ quadraticPlanCost π

def IsUniqueQuadraticOptimalMap {d : ℕ} (ρ μ : Measure (E d))
    (T : E d → E d) : Prop :=
  IsQuadraticOptimalMap ρ μ T ∧
    ∀ π : Measure (E d × E d),
      IsCoupling ρ μ π →
        quadraticPlanCost π ≤ quadraticPlanCost (graphPlan ρ T) →
          π = graphPlan ρ T

def mapL2Dist {d : ℕ} (ρ : Measure (E d))
    (T S : E d → E d) : ℝ :=
  Real.sqrt (∫ x, ‖T x - S x‖ ^ 2 ∂ρ)

def cube (d : ℕ) : Set (E d) :=
  {x | ∀ i, |x i| ≤ 1}

def HasExactlyThreeAtoms {d : ℕ} (μ : Measure (E d))
    (Y : Set (E d)) : Prop :=
  ∃ y : Fin 3 → E d, Function.Injective y ∧
    (∀ i, y i ∈ Y) ∧
    ∃ w : Fin 3 → ℝ≥0∞, (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧
      μ = ∑ i, (w i) • Measure.dirac (y i)

end Problem358

end

end OAI
