import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Distribution
import OAI.Probability.CriticalPercolation.Modular.DensityModular

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_mul_ge_real (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf : Monotone f) (hg : Monotone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω * g ω) := by
  classical
  let l := Finset.univ.inf' Finset.univ_nonempty f
  let k := Finset.univ.inf' Finset.univ_nonempty g
  have hb := expect_mul_ge w hw hpos (fun ω => f ω-l) (fun ω => g ω-k)
    (fun ω => sub_nonneg.mpr (Finset.inf'_le _ (Finset.mem_univ ω)))
    (fun ω => sub_nonneg.mpr (Finset.inf'_le _ (Finset.mem_univ ω)))
    (fun _ _ h => sub_le_sub_right (hf h) l) (fun _ _ h => sub_le_sub_right (hg h) k)
  have he : (fun ω => (f ω-l)*(g ω-k)) =
      (fun ω => f ω*g ω - l*g ω - k*f ω + l*k) := by funext ω; ring
  rw [he, expect_sub, expect_sub, expect_const w hw l, expect_const w hw k,
    expect_add, expect_sub, expect_sub, expect_const_mul, expect_const_mul,
    expect_const w hw (l*k)] at hb
  nlinarith

end CriticalPercolation.FiniteProduct

end
end

end OAI
