import Mathlib
import OAI.Geometry.HyperbolicGroups.PolygonTarget
import OAI.Geometry.HyperbolicGroups.WordPictureBase

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C L V : Type*} (B : PolygonTarget.Boundary C L V)

/-- The literal positive indexed attaching word, with no quotienting of
repeated labels or cyclic starting positions. -/
def positiveSides (c : C) : List B.Side :=
  (List.finRange (B.size c)).map (fun i => ⟨c,true,i⟩)

def attachingWord (c : C) : List L := List.ofFn (B.label c)

lemma positiveSides_boundary (c : C) : IsBoundary B.next (B.positiveSides c) := by
  change IsBoundary B.next ((List.finRange (B.size c)).map (fun i => (⟨c,true,i⟩ : B.Side)))
  apply (finRange_boundary (B.size c)).map (fun i : Fin (B.size c) => (⟨c,true,i⟩ : B.Side))
  · intro x y h
    exact Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2) |>.2
  · intro x
    rfl

lemma positiveSides_label (c : C) : (B.positiveSides c).map B.sideLabel = B.attachingWord c := by
  simp only [positiveSides,List.map_map,sideLabel,Function.comp_def,ite_true]
  exact List.ofFn_eq_map.symm

lemma positiveSides_mem (c : C) {s : B.Side} (hs : s ∈ B.positiveSides c) :
    s.1 = c ∧ s.2.1 = true := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  exact ⟨rfl,rfl⟩

variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → L)
  (closed : ∀ i, B.start (word (finRotate ell i)) = B.start (B.rev (word i)))

/-- A single additional outside polygon, with a separate cell index. -/
def withOutside : PolygonTarget.Boundary (C ⊕ Unit) L V where
  size := Sum.elim B.size (fun _ => ell)
  positive := by rintro (c | c); exact B.positive c; exact hell
  label := fun c => match c with | .inl c => B.label c | .inr _ => word
  start := B.start
  rev := B.rev
  inv := B.inv
  closed := by rintro (c | c) i; exact B.closed c i; exact closed i

/-- `none` marks every genuine target cell, while the two exterior
orientations remain separately identifiable. -/
def outsideTag : (B.withOutside ell hell word closed).Side → Option Bool :=
  fun s => match s.1 with | .inl _ => none | .inr _ => some s.2.1

lemma positive_inside_tag (c : C) (s : (B.withOutside ell hell word closed).Side)
    (hs : s ∈ (B.withOutside ell hell word closed).positiveSides (.inl c)) :
    B.outsideTag ell hell word closed s = none ∧
    B.outsideTag ell hell word closed ((B.withOutside ell hell word closed).opposite s) = none := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  exact ⟨rfl,rfl⟩

lemma positive_outside_tag (s : (B.withOutside ell hell word closed).Side)
    (hs : s ∈ (B.withOutside ell hell word closed).positiveSides (.inr ())) :
    B.outsideTag ell hell word closed s = some true := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
  rfl

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

section

end
end

end OAI
