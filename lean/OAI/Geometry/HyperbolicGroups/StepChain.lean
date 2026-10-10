import Mathlib
import OAI.Geometry.HyperbolicGroups.PermErasePair

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D A : Type*} [DecidableEq D] [Fintype D] [AddCommMonoid A]

/-- Common-side cancellation and backtrack removal retain the EXACT sum of
oriented elementary cone triangles, with arbitrary additive coefficients. -/
lemma sum_offPair {a b : D} (hab : a ≠ b) (q : D → A) (hq : q a + q b = 0) :
    ∑ x : {x // OffPair a b x}, q x.val = ∑ x : D, q x := by
  have hs := Finset.sum_compl_add_sum ({a,b} : Finset D) q
  have hc : ∑ x ∈ ({a,b} : Finset D), q x = 0 := by simp [hab,hq]
  rw [hc,add_zero] at hs
  rw [← hs]
  symm
  exact Finset.sum_subtype _ (by intro x; simp [OffPair]) q

end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
