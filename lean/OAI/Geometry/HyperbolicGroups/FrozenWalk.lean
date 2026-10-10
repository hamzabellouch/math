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

/-- Additional literal boundary indexing for the cells which are not free
macro walks. No normalization property is packaged into this data. -/
structure FrozenTarget (T : WalkCellTarget S C W L V A) where
  next : Perm S
  reverse : Perm S
  reverse_eq : ∀ s, reverse s = T.opposite s
  reverse_sq : reverse * reverse = 1
  reverse_next : ∀ s, reverse (next s) = next⁻¹ (reverse s)
  opposite_cycle : ∀ s, ¬ next.SameCycle s (reverse s)
  opposite_weight : ∀ s, T.weight s + T.weight (reverse s) = 0

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

abbrev FrozenDart := {x : P.Dart // T.free (T.kind (P.index x)) = false}

def frozenFace : Perm P.FrozenDart := P.pairing.face.subtypePerm (by
  intro x
  change T.free ((T.kind ∘ P.index) (P.pairing.face x)) = false ↔ _
  rw [P.kind]; rfl)

lemma frozenFace_val (x : P.FrozenDart) : (P.frozenFace x).val = P.pairing.face x.val := rfl

/-- Frozen source faces use one complete indexed side cycle, without wrapping.
This property is imposed on raw cellular face maps, not on their reducedness. -/
def FrozenMapped (B : FrozenTarget T) : Prop :=
  IndexedFaceMap P.frozenFace B.next (P.index ∘ Subtype.val)

/-- Retain every surviving step, without changing any surviving frozen face.
Unlike the stronger `Retains`, this permits cancellation of entire frozen
faces. Protected outside faces will be retained separately at that boundary. -/
structure Survives (Q : WalkPicture.{u} T) where
  map : Q.Dart → P.Dart
  injective : Function.Injective map
  index : ∀ x, Q.index x = P.index (map x)
  face : ∀ x, T.free (T.kind (Q.index x)) = false →
    map (Q.pairing.face x) = P.pairing.face (map x)

variable {P}
def Retains.survives {Q : WalkPicture.{u} T} (h : P.Retains Q) : P.Survives Q :=
  ⟨h.map,h.injective,h.index,h.face⟩

variable (P)
def Survives.refl : P.Survives P :=
  ⟨id,Function.injective_id,fun _ => rfl,fun _ _ => rfl⟩

def Survives.trans {Q R : WalkPicture.{u} T} (hPQ : P.Survives Q) (hQR : Q.Survives R) :
    P.Survives R := by
  refine ⟨hPQ.map ∘ hQR.map,hPQ.injective.comp hQR.injective,?_,?_⟩
  · intro x; exact (hQR.index x).trans (hPQ.index (hQR.map x))
  · intro x hx
    change hPQ.map (hQR.map (R.pairing.face x)) = _
    rw [hQR.face x hx]
    exact hPQ.face (hQR.map x) (by rw [← hQR.index]; exact hx)

lemma Survives.frozenMapped {Q : WalkPicture.{u} T} (h : P.Survives Q)
    (B : FrozenTarget T) (hm : P.FrozenMapped B) : Q.FrozenMapped B := by
  let j : Q.FrozenDart → P.FrozenDart := fun x =>
    ⟨h.map x.val,by rw [← h.index]; exact x.property⟩
  have hj : ∀ x, j (Q.frozenFace x) = P.frozenFace (j x) := by
    intro x; apply Subtype.ext; exact h.face x.val x.property
  constructor
  · intro x
    change Q.index (Q.pairing.face x.val) = B.next (Q.index x.val)
    rw [h.index,h.face x.val x.property,h.index x.val]
    exact hm.commute (j x)
  · intro x y hxy he
    apply Subtype.ext
    apply h.injective
    have hh := hm.injective (semiconj_perm_sameCycle hj hxy)
    apply congrArg Subtype.val (hh ?_)
    change P.index (h.map x.val) = P.index (h.map y.val)
    rw [← h.index,← h.index]
    exact he

lemma opposite_frozen {a b : P.Dart} (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index b = T.opposite (P.index a)) : T.free (T.kind (P.index b)) = false := by
  rw [hop,T.opposite_kind]; exact ha

/-- Opposite frozen indexed sides determine the COMPLETE opposite faces,
inside the ambient mixed free/frozen picture. -/
theorem frozen_opposite_faces (B : FrozenTarget T) (hm : P.FrozenMapped B)
    (a b : P.Dart) (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index b = T.opposite (P.index a)) :
    let a' : P.FrozenDart := ⟨a,ha⟩
    let I := {x : P.FrozenDart // P.frozenFace.SameCycle a' x}
    ∃ q : Perm I, ∃ v : I → P.Dart,
      PictureMap.OppositeFaces P.pairing.face q (fun x => x.val.val) v ∧
      v ⟨a',SameCycle.rfl⟩ = b ∧ ∀ x, P.index (v x) = T.opposite (P.index x.val.val) := by
  dsimp only
  let a' : P.FrozenDart := ⟨a,ha⟩
  let b' : P.FrozenDart := ⟨b,P.opposite_frozen ha hop⟩
  obtain ⟨q,v,hF,hb,hv⟩ := hm.opposite_faces B.reverse B.reverse_sq B.reverse_next
    B.opposite_cycle a' b' (by change P.index b = B.reverse (P.index a); rw [B.reverse_eq]; exact hop)
  refine ⟨q,fun x => (v x).val,?_,congrArg Subtype.val hb,?_⟩
  · refine ⟨Subtype.val_injective.comp Subtype.val_injective,
      Subtype.val_injective.comp hF.b_inj,?_,?_,?_,hF.cyclic⟩
    · intro x y he
      exact hF.disjoint x y (Subtype.ext he)
    · intro x
      exact congrArg Subtype.val (hF.a_face x)
    · intro x
      exact congrArg Subtype.val (hF.b_face x)
  · intro x
    exact (hv x).trans (B.reverse_eq _)

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
