import Mathlib
import OAI.Geometry.BallPacking.Rigidity.TwoBallBound
import OAI.Geometry.BallPacking.Packings.ComplementPacking

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking

 theorem HasPacking.strict_pair_bound {n k : ℕ} (hn : 3≤n)
    {R : ℝ} {r : Fin k → ℝ} (hR : 0<R) (hr : ∀ i,0<r i)
    (hp : HasPacking n k R r) (i j : Fin k) (hij : i≠j) : r i+r j<R := by
  by_contra hbad
  obtain ⟨a,b,ha,hb,hab,hpab⟩ := hp.unit_pair_counterexample hR hr hij (le_of_not_gt hbad)
  exact (not_le_of_gt hab) (normalized_two_ball_bound n hn a b ha hb hpab)

 theorem main_theorem (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k)
    (R : ℝ) (r : Fin k → ℝ) (hR : 0 < R) (hr : ∀ i, 0 < r i) :
    HasPacking n k R r ↔ PackingInequalities n k R r := by
  constructor
  · intro hp
    exact ⟨hp.volume_lt (by omega) hR hr,hp.strict_pair_bound hn hR hr⟩
  · exact hasPacking_of_inequalities hn hk hR hr

end HigherDimensionalBallPacking

end

end OAI
