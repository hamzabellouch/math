import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Prob

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_disjoint_le (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (P Q R : Set E → Prop) (hP : ∀ ω, P ω → R ω) (hQ : ∀ ω, Q ω → R ω)
    (hPQ : ∀ ω, ¬(P ω ∧ Q ω)) : prob w P + prob w Q ≤ prob w R := by
  unfold prob
  rw [← expect_add]
  apply expect_mono hp
  intro ω
  by_cases hp' : P ω <;> by_cases hq' : Q ω <;> by_cases hr' : R ω <;>
    simp [hp',hq',hr']
  · exact (hPQ ω ⟨hp',hq'⟩).elim
  · exact (hr' (hP ω hp')).elim
  · exact (hr' (hP ω hp')).elim
  · exact (hr' (hQ ω hq')).elim

end CriticalPercolation.FiniteProduct

end
end

end OAI
