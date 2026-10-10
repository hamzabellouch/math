import OAI.Geometry.EinsteinFour.ScalarL2BoundedMultiplier
import Mathlib.Topology.Algebra.Order.Group

namespace OAI

/-! Passing finite coordinate domination inequalities through a dense H1 map. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

variable {X E D : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarL2_closed_domination (A : E →L[ℝ] Lp ℝ 2 μ)
    (B : Fin 4 → E →L[ℝ] Lp ℝ 2 μ) (C : ℝ) (f : D → E)
    (hd : DenseRange f)
    (hb : ∀ a, |A (f a)| ≤ C • ∑ i, |B i (f a)|) (u : E) :
    |A u| ≤ C • ∑ i, |B i u| := by
  have hA : Continuous (fun u => |A u|) := A.continuous.sup A.continuous.neg
  have hB (i : Fin 4) : Continuous (fun u => |B i u|) :=
    (B i).continuous.sup (B i).continuous.neg
  have hc : IsClosed {u : E | |A u| ≤ C • ∑ i, |B i u|} :=
    isClosed_le hA ((continuous_finsetSum _ (fun i _ => hB i)).const_smul C)
  exact hd.induction_on u hc hb

end
end PositiveEinsteinFour.Geometry

end OAI
