import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.ExposureLaw

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E]

lemma exposureLaw_support (w : E → A → ℝ) (D : Set E) (σ ω : E → A)
    (hω : density (exposureLaw w D σ) ω ≠ 0) : ∀ e ∈ D, ω e = σ e := by
  intro e he
  by_contra hb
  apply hω
  unfold density
  exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [exposureLaw,he,hb])

end CriticalPercolation.FiniteProduct

end
end

end OAI
