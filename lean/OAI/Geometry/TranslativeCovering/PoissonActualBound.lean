import OAI.Geometry.TranslativeCovering.PoissonLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace PoissonActualBound
open Set MeasureTheory PoissonConfig PoissonDiagrams
open scoped Classical BigOperators ENNReal NNReal
variable {Ω : Type u_1} {A : Type u_2} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable [Fintype A] [Nonempty A] {I : A → Type u_3}
variable [∀ a, Fintype (I a)] [∀ a, Nonempty (I a)]

theorem lower_tail (r : ℝ≥0) (σ : Measure Ω) [IsProbabilityMeasure σ]
    [NullSingletonClass σ] (E : ∀ a, I a → Set Ω)
    (hE : ∀ a i, MeasurableSet (E a i))
    (hpos : ∀ a i, 0 < (((r : ℝ≥0∞) • σ).real (E a i))) :
    (0 < ∑ a, ∑ b, diagram ((r : ℝ≥0∞) • σ) (E a) (E b)) ∧
    (PoissonSample.simpleSample r σ).real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
      (-(∑ a, ∏ i, ((r : ℝ≥0∞) • σ).real (E a i))^2 /
        (2 * (∑ a, ∑ b, diagram ((r : ℝ≥0∞) • σ) (E a) (E b)))) :=
  by
    have : IsFiniteMeasure ((r : ℝ≥0∞) • σ) := ⟨by
      simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      exact ENNReal.coe_lt_top⟩
    have : NullSingletonClass ((r : ℝ≥0∞) • σ) := ⟨by
      intro x
      simp only [Measure.smul_apply, measure_singleton, smul_zero]⟩
    exact PoissonLimit.lower_tail ((r : ℝ≥0∞) • σ) (PoissonSample.simpleSample r σ)
      (PoissonSample.simpleSample_void r σ) E hE hpos

end PoissonActualBound

end OAI
