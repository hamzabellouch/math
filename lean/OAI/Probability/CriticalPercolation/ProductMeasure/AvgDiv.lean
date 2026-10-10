import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteMarkovAvg

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteMarkov
variable {X : Type*} [Fintype X]

lemma avg_div (μ : X → ℝ) (a : ℝ) (f : X → ℝ) :
    avg (fun x => μ x/a) f = avg μ f/a := by
  simp only [avg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma stationary_of_avg (K : X → X → ℝ) (μ : X → ℝ)
    (h : ∀ f : X → ℝ, avg μ (step K f) = avg μ f) (y : X) :
    ∑ x, μ x * K x y = μ y := by
  classical
  simpa [step, avg] using h (fun x => if x = y then 1 else 0)

end CriticalPercolation.FiniteMarkov

end
end

end OAI
