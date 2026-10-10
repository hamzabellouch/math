import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasure

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
namespace Attempt4FullFar
open Set
open scoped ContDiff Topology
 theorem complex_iteratedDeriv_tsupport (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset).trans ih

end Attempt4FullFar
end
end

end OAI
