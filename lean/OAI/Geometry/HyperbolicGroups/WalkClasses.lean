import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFace
import OAI.Geometry.HyperbolicGroups.WalkCell

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

abbrev Face := Quotient (SameCycle.setoid P.pairing.face)
abbrev Vertex := Quotient (SameCycle.setoid P.pairing.vertex)
noncomputable instance : Fintype P.Face := Fintype.ofFinite _
noncomputable instance : Fintype P.Vertex := Fintype.ofFinite _

def faceClass (x : P.Dart) : P.Face := Quotient.mk _ x
def vertexClass (x : P.Dart) : P.Vertex := Quotient.mk _ x

lemma faceClass_eq {x y : P.Dart} : P.faceClass x = P.faceClass y ↔ P.pairing.face.SameCycle x y :=
  Quotient.eq
lemma vertexClass_eq {x y : P.Dart} : P.vertexClass x = P.vertexClass y ↔ P.pairing.vertex.SameCycle x y :=
  Quotient.eq

lemma faceClass_out (x : P.Face) : P.faceClass x.out = x := Quotient.out_eq _
lemma vertexClass_out (x : P.Vertex) : P.vertexClass x.out = x := Quotient.out_eq _

lemma kind_cycle {x y : P.Dart} (h : P.pairing.face.SameCycle x y) :
    T.kind (P.index x) = T.kind (P.index y) := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm C)) P.kind h)

def faceKind : P.Face → C := Quotient.lift (T.kind ∘ P.index) (fun _ _ h => P.kind_cycle h)
lemma faceKind_mk (x : P.Dart) : P.faceKind (P.faceClass x) = T.kind (P.index x) := rfl

abbrev Link (z : P.Vertex) := {x : P.Dart // P.vertexClass x = z}

def linkNext (z : P.Vertex) : Perm (P.Link z) := P.pairing.vertex⁻¹.subtypePerm (by
  intro x
  have he : P.vertexClass (P.pairing.vertex⁻¹ x) = P.vertexClass x :=
    (P.vertexClass_eq).mpr (sameCycle_inv.mp ((SameCycle.rfl (x := x)).apply_left))
  rw [he])

lemma linkNext_val (z : P.Vertex) (x : P.Link z) : (P.linkNext z x).val = P.pairing.vertex⁻¹ x.val := rfl

lemma link_cyclic (z : P.Vertex) (x y : P.Link z) : ∃ k : ℕ, (P.linkNext z ^ k) x = y := by
  have hh : P.pairing.vertex⁻¹.SameCycle x.val y.val :=
    sameCycle_inv.mpr ((P.vertexClass_eq).mp (x.property.trans y.property.symm))
  have h : (P.linkNext z).SameCycle x y := hh.subtypePerm
  obtain ⟨k,_,_,hk⟩ := h.exists_pow_eq
  exact ⟨k,hk⟩

lemma link_card (z : P.Vertex) :
    Fintype.card (P.Link z) = Fintype.card {x : P.Dart // P.pairing.vertex.SameCycle z.out x} := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [← P.vertexClass_eq,P.vertexClass_out]
  exact eq_comm

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
