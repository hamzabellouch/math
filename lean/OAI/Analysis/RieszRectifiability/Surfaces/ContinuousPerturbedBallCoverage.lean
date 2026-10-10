import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds
import FixedPointTheorems.brouwer

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem closedBall_covered_by_continuous_perturbation {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (a : X) (r δ : ℝ) (hr : 0 ≤ r)
    (f : closedBall a r → X) (hf : Continuous f)
    (hdisp : ∀ x, dist (f x) x.val ≤ δ) :
    closedBall a (r - δ) ⊆ Set.range f := by
  intro z hz
  have hz' : ‖z - a‖ ≤ r - δ := by
    simpa only [mem_closedBall, dist_eq_norm] using! hz
  have hmaps (x : closedBall a r) : z - (f x - x.val) ∈ closedBall a r := by
    change dist (z - (f x - x.val)) a ≤ r
    calc
      _ = ‖(z - a) - (f x - x.val)‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ ≤ ‖z - a‖ + ‖f x - x.val‖ := norm_sub_le _ _
      _ ≤ (r - δ) + δ := add_le_add hz'
        (by simpa only [dist_eq_norm] using! hdisp x)
      _ = r := by ring
  let T : C(closedBall a r, closedBall a r) :=
    ⟨fun x => ⟨z - (f x - x.val), hmaps x⟩,
      (continuous_const.sub (hf.sub continuous_subtype_val)).subtype_mk _⟩
  obtain ⟨u, hu⟩ := _root_.brouwer_fixed_point (closedBall a r)
    (convex_closedBall a r) (isCompact_closedBall a r)
    ⟨a, mem_closedBall_self hr⟩ T
  have heq := congrArg (fun x : closedBall a r => x.val) hu
  change z - (f u - u.val) = u.val at heq
  refine ⟨u, ?_⟩
  calc
    f u = (f u - u.val) + u.val := (sub_add_cancel _ _).symm
    _ = (f u - u.val) + (z - (f u - u.val)) :=
      congrArg (fun w => (f u - u.val) + w) heq.symm
    _ = z := by abel

end

end RieszRectifiability

end OAI
