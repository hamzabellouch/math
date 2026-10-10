import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.AffineDirectionCounting

namespace OAI

namespace Balanced.ProjectionGuardRegression684a

theorem identical_lines_two_successes :
    ((Finset.univ : Finset (Direction (ZMod 2))).filter (fun d =>
      d ≠ (none : Direction (ZMod 2)) ∧
      lineIntersection (none, (1 : ZMod 2)) (lineThrough d (0,0)) ≠ (0,0) ∧
      OnLine (lineIntersection (none, (1 : ZMod 2)) (lineThrough d (0,0)))
        (none, (1 : ZMod 2)))).card = 2 := by
  decide

theorem centre_intersection_two_successes :
    ((Finset.univ : Finset (Direction (ZMod 2))).filter (fun d =>
      d ≠ (none : Direction (ZMod 2)) ∧
      OnLine (lineIntersection (none, (0 : ZMod 2)) (lineThrough d (0,0)))
        (some 0, (0 : ZMod 2)))).card = 2 := by
  decide

theorem centre_intersection_guarded_zero :
    ((Finset.univ : Finset (Direction (ZMod 2))).filter (fun d =>
      d ≠ (none : Direction (ZMod 2)) ∧
      lineIntersection (none, (0 : ZMod 2)) (lineThrough d (0,0)) ≠ (0,0) ∧
      OnLine (lineIntersection (none, (0 : ZMod 2)) (lineThrough d (0,0)))
        (some 0, (0 : ZMod 2)))).card = 0 := by
  decide

end Balanced.ProjectionGuardRegression684a

end OAI
