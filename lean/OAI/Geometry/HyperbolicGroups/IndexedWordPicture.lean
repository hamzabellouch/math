import Mathlib
import OAI.Geometry.HyperbolicGroups.PolygonTarget
import OAI.Geometry.HyperbolicGroups.WordPicture

namespace OAI

/-! Persistent cell identities on word pictures. Unlike a bare relator witness,
this marking remembers which actual cell each interior face uses. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*}
  {R : Set (Word E)} {w : Word E}
  (B : PolygonTarget.Boundary C (E × Bool) V) (P : WordPicture R w)

structure Indexing where
  index : P.Dart → Option B.Side
  outside : ∀ x, index x = none ↔ x ∈ P.outside
  commute : ∀ x, index (P.pairing.face x) = (index x).map B.next
  injective : ∀ {x y : P.Dart}, P.pairing.face.SameCycle x y →
    ∀ s, index x = some s → index y = some s → x = y
  label : ∀ x s, index x = some s → P.label x = B.sideLabel s

namespace Indexing
variable {B P} (I : Indexing B P)

include I in
lemma outside_face (x : P.Dart) : P.pairing.face x ∈ P.outside ↔ x ∈ P.outside := by
  rw [← I.outside, I.commute, Option.map_eq_none_iff, I.outside]

lemma commute_inv (x : P.Dart) :
    I.index (P.pairing.face⁻¹ x) = (I.index x).map B.next.symm := by
  have hh := I.commute (P.pairing.face⁻¹ x)
  simp only [Perm.inv_def,Equiv.apply_symm_apply] at hh
  rw [hh,Option.map_map]
  simp only [Function.comp_def,Perm.inv_def,Equiv.symm_apply_apply]
  cases I.index (P.pairing.face.symm x) <;> rfl

lemma reverse_prev (s : B.Side) : B.opposite (B.next⁻¹ s) = B.next (B.opposite s) := by
  have hh := congrArg B.next (B.reverse_next (B.next⁻¹ s))
  simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hh.symm

def mirror (hrev : B.rev = invLetter) : Indexing B P.mirror where
  index x := (I.index x).map B.opposite
  outside x := by
    change P.Dart at x
    change (I.index x).map B.opposite = none ↔ x ∈ P.outside.reverse
    rw [Option.map_eq_none_iff,I.outside,List.mem_reverse]
  commute x := by
    change P.Dart at x
    change (I.index (P.pairing.face⁻¹ x)).map B.opposite = _
    rw [I.commute_inv,Option.map_map,Option.map_map]
    congr 1
    funext s
    exact reverse_prev s
  injective hxy s hx hy := by
    obtain ⟨a,ha,has⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨b,hb,hbs⟩ := Option.map_eq_some_iff.mp hy
    have he : a = b := B.opposite.injective (has.trans hbs.symm)
    exact I.injective (sameCycle_inv.mp hxy) a ha (he ▸ hb)
  label x s hx := by
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hx
    change invLetter (P.label x) = _
    rw [I.label x a ha,B.edge_opposite,hrev]

variable {A : Type*} [AddCommGroup A]

/-- Count one marked corner of every interior face. Exterior corners contribute
zero. This uses independent cell coefficients, not the word image. -/
def cornerWeight (weight : C → A) (s : Option B.Side) : A :=
  match s with
  | none => 0
  | some s => if s.2.2.val = 0 then B.weight weight s else 0

def chain (weight : C → A) : A := ∑ x : P.Dart, cornerWeight weight (I.index x)

lemma cornerWeight_opposite (weight : C → A) (s : Option B.Side) :
    cornerWeight weight (s.map B.opposite) = - cornerWeight weight s := by
  cases s with
  | none => exact (neg_zero).symm
  | some s =>
    rcases s with ⟨c,b,i⟩
    by_cases hi : i.val = 0 <;> cases b <;>
      simp [cornerWeight,PolygonTarget.Boundary.opposite,PolygonTarget.Boundary.weight,hi]

lemma mirror_chain (hrev : B.rev = invLetter) (weight : C → A) :
    (I.mirror hrev).chain weight = - I.chain weight := by
  change (∑ x : P.Dart, cornerWeight weight ((I.index x).map B.opposite)) = _
  simp only [cornerWeight_opposite,Finset.sum_neg_distrib,chain]

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
