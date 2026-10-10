import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFace
import OAI.Geometry.HyperbolicGroups.PolygonSphere

namespace OAI

section
section
noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D B : Type*}

namespace PolygonSphere
variable {I : Type*} (q : Perm I)

def turn : Perm (Bool × I) where
  toFun x := (x.1,if x.1 then q x.2 else q⁻¹ x.2)
  invFun x := (x.1,if x.1 then q⁻¹ x.2 else q x.2)
  left_inv := by rintro ⟨b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]
  right_inv := by rintro ⟨b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]

def flip : Perm (Bool × I) where
  toFun x := (!x.1,x.2)
  invFun x := (!x.1,x.2)
  left_inv := by rintro ⟨b,i⟩; cases b <;> rfl
  right_inv := by rintro ⟨b,i⟩; cases b <;> rfl

/-- The sphere obtained by pairing a polygon with a reversed copy. It is the
literal base case of a cellular disk picture after adjoining its outside. -/
def pairing : PictureMap (Bool × I) where
  face := turn q
  edge := flip
  edge_sq := by apply Equiv.ext; rintro ⟨b,i⟩; cases b <;> rfl
  edge_ne := by rintro ⟨b,i⟩ he; cases b <;> exact Bool.noConfusion (congrArg Prod.fst he)

lemma turn_orientation (x : Bool × I) : (turn q x).1 = x.1 := rfl

lemma face_sameCycle_pos {i j : I} (h : q.SameCycle i j) :
    (turn q).SameCycle (true,i) (true,j) :=
  semiconj_perm_sameCycle (j := fun i => (true,i)) (fun _ => rfl) h

lemma face_sameCycle_neg {i j : I} (h : q.SameCycle i j) :
    (turn q).SameCycle (false,i) (false,j) :=
  semiconj_perm_sameCycle (j := fun i => (false,i)) (fun _ => rfl) h.inv

lemma face_classes (hq : ∀ i j, q.SameCycle i j) (x y : Bool × I) :
    (turn q).SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · intro h
    exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm Bool))
      (j := Prod.fst) (turn_orientation q) h)
  · rcases x with ⟨b,i⟩; rcases y with ⟨c,j⟩
    intro h
    cases h
    cases b
    · exact face_sameCycle_neg q (hq i j)
    · exact face_sameCycle_pos q (hq i j)

/-- Vertex classifier for the doubled boundary: vertices are NOT assumed as
incidence fields; they are computed from face-turn times side-pairing. -/
def vertexIndex (x : Bool × I) : I := if x.1 then x.2 else q x.2

lemma vertex_index (x : Bool × I) : vertexIndex q ((pairing q).vertex x) = vertexIndex q x := by
  rcases x with ⟨b,i⟩; cases b <;> simp [vertexIndex,PictureMap.vertex,pairing,turn,flip]

lemma vertex_classes (x y : Bool × I) :
    (pairing q).vertex.SameCycle x y ↔ vertexIndex q x = vertexIndex q y := by
  constructor
  · intro h
    exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm I))
      (j := vertexIndex q) (vertex_index q) h)
  · rcases x with ⟨b,i⟩; rcases y with ⟨c,j⟩
    cases b <;> cases c <;> intro h
    · have he : i = j := q.injective h
      subst j
      exact SameCycle.rfl
    · have he : q i = j := h
      subst j
      exact SameCycle.rfl.apply_right
    · have he : i = q j := h
      subst i
      have h' : (pairing q).vertex (true,q j) = (false,j) := by
        simp [PictureMap.vertex,pairing,turn,flip]
      exact h' ▸ (SameCycle.rfl (x := (true,q j))).apply_right
    · have he : i = j := h
      subst j
      exact SameCycle.rfl

variable [Fintype I]

lemma connected (hq : ∀ i j, q.SameCycle i j) (x y : Bool × I) :
    (pairing q).components x y := by
  have h₁ : (pairing q).components x (true,y.2) := by
    rcases x with ⟨b,i⟩
    cases b
    · exact (pairing q).components.trans'
        ((pairing q).edge_le_components (SameCycle.rfl (x := (false,i))).apply_right)
        ((pairing q).face_le_components (face_sameCycle_pos q (hq i y.2)))
    · exact (pairing q).face_le_components (face_sameCycle_pos q (hq i y.2))
  have h₂ : (pairing q).components (true,y.2) y := by
    rcases y with ⟨b,j⟩; cases b
    · exact (pairing q).edge_le_components (SameCycle.rfl (x := (true,j))).apply_right
    · exact (pairing q).components.refl' _
  exact (pairing q).components.trans' h₁ h₂

theorem genusZero [DecidableEq I] (hq : ∀ i j, q.SameCycle i j) (i₀ : I) : (pairing q).GenusZero := by
  have hf : cycles (pairing q).face = 2 := by
    change cycles (turn q) = 2
    have h := cycles_of_classifier (turn q) Prod.fst (face_classes q hq) (fun b => ⟨(b,i₀),rfl⟩)
    simpa using h
  have hv : cycles (pairing q).vertex = Fintype.card I :=
    cycles_of_classifier _ (vertexIndex q) (vertex_classes q) (fun i => ⟨(true,i),rfl⟩)
  have hc : Nat.card (Quotient (pairing q).components) = 1 := by
    have h := card_quotient_of_classifier (pairing q).components (fun _ => ())
      (fun x y => ⟨fun _ => rfl,fun _ => connected q hq x y⟩) (fun _ => ⟨(true,i₀),rfl⟩)
    simpa using h
  change (pairing q).euler = 2 * (Nat.card (Quotient (pairing q).components) : ℤ)
  rw [PictureMap.euler,hf,hv,hc,Fintype.card_prod,Fintype.card_bool]
  push_cast
  omega

end PolygonSphere
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
