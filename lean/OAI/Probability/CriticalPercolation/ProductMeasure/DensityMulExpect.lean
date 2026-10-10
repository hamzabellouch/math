import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma density_mul_le_expect {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) (ω : E → A) :
    density w ω * f ω ≤ expect w f := by
  classical
  exact Finset.single_le_sum (fun ω _ => mul_nonneg (density_nonneg hw ω) (hf ω))
    (Finset.mem_univ ω)
end CriticalPercolation.FiniteProduct

end
end

end OAI
