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

lemma prob_or (w : E → Prop → ℝ) (P Q : Set E → Prop)
    (hd : ∀ ω, ¬(P ω ∧ Q ω)) :
    prob w (fun ω => P ω ∨ Q ω) = prob w P + prob w Q := by
  unfold prob
  rw [← expect_add]
  apply congrArg (expect w)
  funext ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]
  exact (hd ω ⟨hp,hq⟩).elim

lemma prob_diff (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w (fun ω => P ω ∧ ¬Q ω) = prob w P - prob w (fun ω => P ω ∧ Q ω) := by
  have hh := prob_split w P Q
  linarith
end CriticalPercolation.FiniteProduct

end
end

end OAI
