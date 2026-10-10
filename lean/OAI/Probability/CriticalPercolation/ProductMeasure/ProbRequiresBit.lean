import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Potential

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_requires_bit (w : E → Prop → ℝ) (e : E) (b : Prop) (P : Set E → Prop)
    (hb : ∀ ω, P ω → ω e = b) : prob w P = w e b*prob (pin w e b) P := by
  have hh := expect_prop_mask_pin w e b (fun ω => if P ω then 1 else 0)
  have he : (fun ω => if ω e = b then (if P ω then (1:ℝ) else 0) else 0) =
      fun ω => if P ω then 1 else 0 := by
    funext ω
    by_cases hp : P ω
    · simp [hp,hb ω hp]
    · simp [hp]
  erw [he] at hh
  exact hh

end CriticalPercolation.FiniteProduct

end
end

end OAI
