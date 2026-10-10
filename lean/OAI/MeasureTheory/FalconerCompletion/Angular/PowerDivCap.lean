import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.RecursiveLoss

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
lemma power_div_cap {N : ℕ} {a b M : ℝ} (hM : 0≤M) (hab : a≤b) :
    ((2:ℝ)^N)^a*(M/((2:ℝ)^N)^b)≤M := by
  apply weighted_child_cap (by positivity) hab
  have hp : 0<((2:ℝ)^N)^b := by positivity
  field_simp; exact le_rfl
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
