import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelWeights

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

theorem activeLevelWeight_sum_eq_one_near_center {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t) (x : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    (∑ i ∈ activeLevelIndex μ R hR k z Good t,
      activeLevelWeight μ R hR k z Good t i x) = 1 := by
  apply finiteNormalizedWeight_sum_eq_one
  have hone : activeLevelCutoff μ R hR k z t q x = 1 :=
    finiteCoverCutoff_eq_one q.center _ (latticeRadius_pos R hR (k + t)) x hx
  rw [← hone]
  exact Finset.single_le_sum (fun i _ => finiteCoverCutoff_nonneg i.center _ x) hq

end

end RieszRectifiability

end OAI
