import Mathlib
import OAI.Geometry.HyperbolicGroups.StarMean
import OAI.Geometry.HyperbolicGroups.PolygonTarget
import OAI.Geometry.HyperbolicGroups.FrozenSideExists

namespace OAI

section


/-! Counting one selected position on each actual indexed face. -/
noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D S A : Type*} [Fintype D] [DecidableEq D] [AddCommMonoid A]

omit [DecidableEq D] in
lemma faceChain_eq_selected (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (p : D → Prop) (hp : ∀ a, ∃! b, f.SameCycle a b ∧ p b) :
    faceChain f w hw = ∑ x : Subtype p, w x.val := by
  let j : Subtype p → Quotient (SameCycle.setoid f) := fun x => Quotient.mk _ x.val
  have hj : Function.Bijective j := by
    constructor
    · intro x y he
      have hxy : f.SameCycle x.val y.val := Quotient.exact he
      obtain ⟨b,hb,hub⟩ := hp x.val
      exact Subtype.ext ((hub x.val ⟨SameCycle.rfl,x.property⟩).trans
        (hub y.val ⟨hxy,y.property⟩).symm)
    · intro q
      induction q using Quotient.inductionOn with | h a =>
        obtain ⟨b,hb,_⟩ := hp a
        exact ⟨⟨b,hb.2⟩,Quotient.sound hb.1.symm⟩
  let e := Equiv.ofBijective j hj
  unfold faceChain classSum
  exact (Fintype.sum_equiv e (fun x : Subtype p => w x.val) _ (fun x => rfl)).symm

omit [DecidableEq D] in
lemma faceChain_eq_ite (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (p : D → Prop) (hp : ∀ a, ∃! b, f.SameCycle a b ∧ p b) :
    faceChain f w hw = ∑ x : D, if p x then w x else 0 := by
  rw [faceChain_eq_selected f w hw p hp]
  exact HyperbolicObstruction.sum_subtype_eq_ite p w

omit [Fintype D] [DecidableEq D] in
lemma IndexedFaceMap.selected (f : Perm D) (t : Perm S) (j : D → S)
    (hm : IndexedFaceMap f t j) (p : S → Prop)
    (hp : ∀ s, ∃! z, t.SameCycle s z ∧ p z) :
    ∀ a, ∃! b, f.SameCycle a b ∧ p (j b) := by
  intro a
  obtain ⟨s,hs,hus⟩ := hp (j a)
  obtain ⟨b,hb,hjb⟩ := hm.orbit_surjective a hs.1
  refine ⟨b,⟨hb,hjb ▸ hs.2⟩,?_⟩
  intro y hy
  have hys := hus (j y) ⟨semiconj_perm_sameCycle hm.commute hy.1,hy.2⟩
  exact hm.injective (hy.1.symm.trans hb) (hys.trans hjb.symm)

namespace PolygonTarget.Boundary
variable {C L V : Type*} (B : Boundary C L V)

lemma cell_cycle {s t : B.Side} (h : B.next.SameCycle s t) : s.1 = t.1 := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle
    (t := (1 : Perm C)) (j := fun s : B.Side => s.1) (fun _ => rfl) h)

lemma marked_unique (mark : ∀ c, Fin (B.size c)) (s : B.Side) :
    ∃! t : B.Side, B.next.SameCycle s t ∧ t.2.2 = mark t.1 := by
  rcases s with ⟨c,b,i⟩
  refine ⟨⟨c,b,mark c⟩,⟨B.side_sameCycle c b i (mark c),rfl⟩,?_⟩
  rintro ⟨a,z,j⟩ ⟨hh,hj⟩
  have ha := B.cell_cycle hh
  have hz := B.orientation_cycle hh
  dsimp at ha hz hj
  subst a; subst z; subst j
  rfl
end PolygonTarget.Boundary
end HyperbolicObstruction.PictureSwitch
end
end

section

end

end OAI
