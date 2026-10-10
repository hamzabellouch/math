import Mathlib
import OAI.Geometry.HyperbolicGroups.MappedPicture
import OAI.Geometry.HyperbolicGroups.PermErasePair
import OAI.Geometry.HyperbolicGroups.EdgeErase

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

lemma erasePair_cycles_le (p : Perm D) {a b : D} (hab : a ≠ b) :
    cycles (erasePair p hab) ≤ cycles p := by
  let q := bypassPair p a b
  have hqA : q a = a := bypassPair_a p hab
  have hqB : q b = b := bypassPair_b p a b
  let s := q.subtypePerm (p := fun x => ¬ OffPair a b x)
    (fun x => not_congr (offPair_invariant hqA hqB x))
  have hc : cycles q = cycles (erasePair p hab) + cycles s := by
    simpa only [cycles_eq_card_classes,erasePair,q,s] using
      (cycles_subtype_split (P := OffPair a b) q (offPair_invariant hqA hqB))
  have hs : s = 1 := by
    ext x
    change q x.val = x.val
    have hx : x.val = a ∨ x.val = b := by
      have hh := x.property
      unfold OffPair at hh
      tauto
    rcases hx with hx | hx
    · rw [hx,hqA]
    · rw [hx,hqB]
  have hcard : Fintype.card {x : D // ¬ OffPair a b x} = 2 := by
    rw [Fintype.card_of_subtype ({a,b} : Finset D) (by intro x; simp only [Finset.mem_insert,Finset.mem_singleton,OffPair]; tauto)]
    simp [hab]
  have hsC : cycles s = 2 := by rw [hs]; simp [cycles,defect,hcard]
  have hqC : cycles q ≤ cycles p + 2 := by
    change cycles (bypass (bypass p a) b) ≤ _
    rw [bypass_cycles,bypass_cycles]
    split_ifs <;> omega
  rw [hsC] at hc
  omega

namespace PictureMap
lemma eraseEdge_faces_le (M : PictureMap D) (a : D)
    (hne : ¬ M.face.SameCycle a (M.edge a)) :
    cycles (M.eraseEdge a).face + 1 ≤ cycles M.face := by
  have h₁ := erasePair_cycles_le (M.face*swap a (M.edge a)) (M.edge_ne a).symm
  have h₂ := cycles_merge_right M.face hne
  change cycles (erasePair (M.face*swap a (M.edge a)) (M.edge_ne a).symm) + 1 ≤ _
  omega
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
