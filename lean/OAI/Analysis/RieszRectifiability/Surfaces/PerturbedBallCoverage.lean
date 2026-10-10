import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Ball coverage by a Lipschitz perturbation

A map with bounded displacement whose error from the identity is a strict
contraction covers a smaller concentric closed ball. A fixed point of the
associated correction map provides the preimage of each target point.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem closedBall_covered_by_lipschitz_perturbation {X : Type*}
    [NormedAddCommGroup X] [CompleteSpace X]
    (a : X) (r δ : ℝ) (hr : 0 ≤ r) (K : ℝ≥0) (hK : K < 1)
    (f : closedBall a r → X)
    (hdisp : ∀ x, dist (f x) x.val ≤ δ)
    (herr : LipschitzWith K (fun x : closedBall a r => f x - x.val)) :
    closedBall a (r - δ) ⊆ Set.range f := by
  intro z hz
  have hz' : ‖z - a‖ ≤ r - δ := by simpa only [mem_closedBall, dist_eq_norm] using! hz
  have hmaps (x : closedBall a r) : z - (f x - x.val) ∈ closedBall a r := by
    change dist (z - (f x - x.val)) a ≤ r
    calc
      _ = ‖(z - a) - (f x - x.val)‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ ≤ ‖z - a‖ + ‖f x - x.val‖ := norm_sub_le _ _
      _ ≤ (r - δ) + δ := add_le_add hz' (by simpa only [dist_eq_norm] using! hdisp x)
      _ = r := by ring
  let T : closedBall a r → closedBall a r :=
    fun x => ⟨z - (f x - x.val), hmaps x⟩
  have hLip : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (z - (f x - x.val)) (z - (f y - y.val)) ≤ K * dist x y
    have heq : (z - (f x - x.val)) - (z - (f y - y.val)) =
        -((f x - x.val) - (f y - y.val)) := by abel
    rw [dist_eq_norm, heq, norm_neg]
    simpa only [dist_eq_norm] using! herr.dist_le_mul x y
  let : CompleteSpace (closedBall a r) :=
    (show IsClosed (closedBall a r) from isClosed_closedBall).isComplete.completeSpace_coe
  have hT : ContractingWith K T := ⟨hK, hLip⟩
  obtain ⟨u, hu, _, _⟩ := hT.exists_fixedPoint ⟨a, mem_closedBall_self hr⟩ (edist_ne_top _ _)
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
