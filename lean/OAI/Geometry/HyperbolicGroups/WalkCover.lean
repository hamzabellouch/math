import Mathlib
import OAI.Geometry.HyperbolicGroups.FaceWalk
import OAI.Geometry.HyperbolicGroups.FrozenWalk
import OAI.Geometry.HyperbolicGroups.FullWalkNormal
import OAI.Geometry.HyperbolicGroups.WalkRadial

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r q p
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

/-- Literal voltage data for a regular cover of the indexed cell target.
`offset` is the position of a side's initial vertex relative to its cell lift.
These are local edge equations, not a chain-vanishing assumption. -/
structure WalkCellCover (T : WalkCellTarget S C W L V A) (G : Type q) [Group G] where
  voltage : L → G
  voltage_rev : ∀ l, voltage (T.rev l) = (voltage l)⁻¹
  offset : S → G
  offset_opposite : ∀ s, offset (T.opposite s) = offset s * voltage (T.label s)
  free_back : ∀ s t, T.free (T.kind s) = true → T.kind s = T.kind t →
    T.back s = T.back t → offset (T.opposite s) = offset (T.opposite t)

namespace WalkCellCover
variable {T : WalkCellTarget S C W L V A} {G : Type q} [Group G]
  (H : WalkCellCover T G) {B : Type p} [AddCommMonoid B]

lemma offset_opposite_opposite (s : S) : H.offset (T.opposite (T.opposite s)) = H.offset s := by
  rw [H.offset_opposite,H.offset_opposite,T.opposite_label,H.voltage_rev,mul_inv_cancel_right]

def target (weight : G → S → B)
    (hw : ∀ g s, T.free (T.kind s) = true → weight g s + weight g (T.opposite s) = 0) :
    WalkCellTarget (G × S) (G × C) (G × W) (G × L) (G × V) B where
  kind s := (s.1,T.kind s.2)
  free c := T.free c.2
  front s := (s.1 * H.offset s.2,T.front s.2)
  back s := (s.1 * H.offset (T.opposite s.2),T.back s.2)
  vertex x := (x.1,T.vertex x.2)
  label s := (s.1 * H.offset s.2,T.label s.2)
  start l := (l.1,T.start l.2)
  rev l := (l.1 * H.voltage l.2,T.rev l.2)
  rev_rev := by intro l; ext <;> simp [T.rev_rev,H.voltage_rev]
  front_label := by intro s; exact Prod.ext rfl (T.front_label s.2)
  back_label := by
    intro s; apply Prod.ext
    · exact (mul_assoc _ _ _).trans (congrArg (s.1 * ·) (H.offset_opposite s.2).symm)
    · exact T.back_label s.2
  opposite s := (s.1,T.opposite s.2)
  opposite_kind := by intro s; exact Prod.ext rfl (T.opposite_kind s.2)
  opposite_front := by intro s; exact Prod.ext rfl (T.opposite_front s.2)
  opposite_back := by
    intro s; exact Prod.ext (congrArg (s.1 * ·) (H.offset_opposite_opposite s.2)) (T.opposite_back s.2)
  opposite_label := by
    intro s; apply Prod.ext
    · exact (congrArg (s.1 * ·) (H.offset_opposite s.2)).trans (mul_assoc _ _ _).symm
    · exact T.opposite_label s.2
  loopless := by intro s hs he; exact T.loopless s.2 hs (congrArg Prod.snd he)
  simple := by
    intro s t hs hk hf hb
    exact Prod.ext (congrArg (fun q : G × C => q.1) hk)
      (T.simple s.2 t.2 hs (congrArg Prod.snd hk) (congrArg Prod.snd hf) (congrArg Prod.snd hb))
  weight s := weight s.1 s.2
  opposite_weight := by intro s hs; exact hw s.1 s.2 hs

variable (weight : G → S → B)
  (hw : ∀ g s, T.free (T.kind s) = true → weight g s + weight g (T.opposite s) = 0)

def frozenTarget (F : FrozenTarget T)
    (hw' : ∀ g s, weight g s + weight g (T.opposite s) = 0) :
    FrozenTarget (H.target weight hw) where
  next := Equiv.prodCongr (Equiv.refl G) F.next
  reverse := Equiv.prodCongr (Equiv.refl G) F.reverse
  reverse_eq := by intro s; exact Prod.ext rfl (F.reverse_eq s.2)
  reverse_sq := by
    apply Equiv.ext; intro s
    change (s.1,F.reverse (F.reverse s.2)) = (s.1,s.2)
    apply Prod.ext
    · rfl
    · exact Equiv.congr_fun F.reverse_sq s.2
  reverse_next := by intro s; exact Prod.ext rfl (F.reverse_next s.2)
  opposite_cycle := by
    intro s hh
    apply F.opposite_cycle s.2
    exact semiconj_perm_sameCycle (j := (Prod.snd : G × S → S)) (fun _ => rfl) hh
  opposite_weight := by
    intro s
    change weight s.1 s.2 + weight s.1 (F.reverse s.2) = 0
    rw [F.reverse_eq]; exact hw' s.1 s.2

variable (P : WalkPicture.{u} (H.target weight hw))

/-- Forget deck coordinates but not a single dart or face. -/
def forget : WalkPicture.{u} T where
  Dart := P.Dart
  pairing := P.pairing
  index x := (P.index x).2
  closed := by intro x; exact congrArg Prod.snd (P.closed x)
  kind := by intro x; exact congrArg Prod.snd (P.kind x)
  paired := by intro x; exact congrArg Prod.snd (P.paired x)
  genusZero := P.genusZero

lemma deck_face {a b : P.Dart} (hab : P.pairing.face.SameCycle a b) :
    (P.index a).1 = (P.index b).1 :=
  congrArg (fun q : G × C => q.1) (PictureMap.kind_cycle P.kind hab)

lemma forget_simple (hs : P.Simple) : (H.forget weight hw P).Simple := by
  intro a b ha hab he
  apply hs a b ha hab
  apply Prod.ext
  · change (P.index a).1 * H.offset (T.opposite (P.index a).2) =
      (P.index b).1 * H.offset (T.opposite (P.index b).2)
    rw [H.deck_face weight hw P hab]
    congr 1
    exact H.free_back _ _ ha (PictureMap.kind_cycle (H.forget weight hw P).kind hab) he
  · exact he

lemma forget_noBigon (hs : P.NoBigon) : (H.forget weight hw P).NoBigon := hs

lemma forget_fullyReduced (hs : P.FullyReduced) : (H.forget weight hw P).FullyReduced := by
  intro a he
  apply hs a
  apply Prod.ext
  · have hp := congrArg Prod.fst (P.paired a)
    change (P.index (P.pairing.edge a)).1 * H.offset (P.index (P.pairing.edge a)).2 =
      ((P.index a).1 * H.offset (P.index a).2) * H.voltage (T.label (P.index a).2) at hp
    change (P.index (P.pairing.edge a)).2 = T.opposite (P.index a).2 at he
    rw [he,H.offset_opposite,mul_assoc] at hp
    exact mul_right_cancel hp
  · exact he

lemma forget_radialInjective (apex : V → Bool)
    (hs : P.RadialInjective (apex ∘ Prod.snd)) :
    (H.forget weight hw P).RadialInjective apex := by
  intro a b ha hab he
  apply hs a b ha hab
  apply Prod.ext
  · have hv := sameCycle_le_of_apply
      (s := Setoid.ker (fun x : P.Dart => (H.target weight hw).start ((H.target weight hw).label (P.index x))))
      (fun x => (P.respects.1 x).symm) hab
    exact congrArg (fun q : G × V => q.1) hv
  · exact he

lemma forget_frozenMapped (F : FrozenTarget T)
    (hw' : ∀ g s, weight g s + weight g (T.opposite s) = 0)
    (hm : P.FrozenMapped (H.frozenTarget weight hw F hw')) :
    (H.forget weight hw P).FrozenMapped F := by
  constructor
  · intro x; exact congrArg Prod.snd (hm.commute x)
  · intro x y hxy he
    apply hm.injective hxy
    apply Prod.ext
    · exact H.deck_face weight hw P (semiconj_perm_sameCycle (j := (Subtype.val : P.FrozenDart → P.Dart)) (fun _ => rfl) hxy)
    · exact he

end WalkCellCover
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
