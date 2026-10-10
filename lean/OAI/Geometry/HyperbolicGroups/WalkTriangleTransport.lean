import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFacePosition
import OAI.Geometry.HyperbolicGroups.WalkInstanceAt
import OAI.Geometry.HyperbolicGroups.FrozenSideExists
import OAI.Geometry.HyperbolicGroups.WalkRadialBoundary

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllTriangleIndex := Σ b : Fan n w,
  (indexedFanData n w d c hc f P select b hs hm hred hrad).TriangleIndex
abbrev triangleCorner (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) := p.2.val.2.val

def triangleRawDart (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) : P.Dart :=
  P.pairing.face (triangleCorner n w d c hc f P select hs hm hred hrad p)

lemma triangle_selected (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) :
    select (P.faceClass (triangleCorner n w d c hc f P select hs hm hred hrad p)) = true := by
  by_contra hh
  have hx := (mark_absent n w d c hc f P select p.1 p.2.val.1 p.2.val.2).mpr hh
  have ht := p.2.property
  change fragmentMark n w d c hc f P select p.1 p.2.val.1 p.2.val.2 = .triangle at ht
  rw [hx] at ht
  cases ht

lemma triangle_raw_index (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) :
    ∃ g o, P.index (triangleRawDart n w d c hc f P select hs hm hred hrad p) =
      .inr ⟨.inl g,o,(1 : Fin 3)⟩ := by
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d c hc f P select p.1 p.2.val.1 p.2.val.2 p.2.property
  have he := hm.commute ⟨p.2.val.2.val,by rw [hx]; rfl⟩
  change P.index (P.pairing.face p.2.val.2.val) =
    (walkFrozenTarget n w d c hc f).next (P.index p.2.val.2.val) at he
  refine ⟨g,o,?_⟩
  change P.index (P.pairing.face p.2.val.2.val) = _
  rw [he,hx]
  cases o <;> rfl

lemma triangleRawDart_injective : Function.Injective
    (triangleRawDart n w d c hc f P select hs hm hred hrad) := by
  intro p q h
  have hh := apexCorner_injective n w d c hc f P select
    (a₁ := ⟨p.1,p.2.val⟩) (a₂ := ⟨q.1,q.2.val⟩) (P.pairing.face.injective h)
  rcases p with ⟨b,x⟩; rcases q with ⟨a,y⟩
  have hb : b = a := congrArg Sigma.fst hh
  subst a
  have hv : x.val = y.val := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))

lemma allTriangleIndex_card :
    Fintype.card (AllTriangleIndex n w d c hc f P select hs hm hred hrad) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles := by
  rw [← Nat.card_eq_fintype_card]
  exact FanLink.IndexedFanData.family_natTriangleIndex_card
    (fun b => indexedFanData n w d c hc f P select b hs hm hred hrad)

abbrev SelectedTriangleFace := {F : P.Face // select F = true ∧
  ∃ g : FanTriangle n w, P.faceKind F = .inr (.inl g)}
noncomputable instance : Fintype (SelectedTriangleFace n w d c hc f P select) := Fintype.ofFinite _

def triangleFace (p : AllTriangleIndex n w d c hc f P select hs hm hred hrad) :
    SelectedTriangleFace n w d c hc f P select := by
  refine ⟨P.faceClass (triangleCorner n w d c hc f P select hs hm hred hrad p),
    triangle_selected n w d c hc f P select hs hm hred hrad p,?_⟩
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d c hc f P select p.1 p.2.val.1 p.2.val.2 p.2.property
  refine ⟨g,?_⟩
  change walkKind n w d (P.index p.2.val.2.val) = _
  rw [hx]
  rfl

lemma triangleFace_surjective : Function.Surjective
    (triangleFace n w d c hc f P select hs hm hred hrad) := by
  intro F
  obtain ⟨g,hg⟩ := F.property.2
  have ho := P.faceClass_out F.val
  have hg' : walkKind n w d (P.index F.val.out) = .inr (.inl g) := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [ho]
    exact hg
  obtain ⟨o,i,hi⟩ : ∃ (o : Bool) (i : Fin 3), P.index F.val.out = .inr ⟨.inl g,o,i⟩ := by
    cases h : P.index F.val.out with
    | inl x => rw [h] at hg'; cases hg'
    | inr s =>
      rcases s with ⟨k,o,i⟩
      have hk : k = .inl g := Sum.inr.inj (by simpa only [h,walkKind] using hg')
      subst k
      exact ⟨o,i,rfl⟩
  obtain ⟨y,hy,he⟩ := frozen_side_exists n w d c hc f P hm hi (if o then (0 : Fin 3) else (2 : Fin 3))
  have hface : P.faceClass y = F.val := ((P.faceClass_eq).mpr hy).symm.trans ho
  have hsel : select (P.faceClass y) = true := by rw [hface]; exact F.property.1
  have hstart : start n w (walkLabel n w d (P.index y)) = .inr g.1 := by
    change P.index y = frozenCorner n w d g o at he
    rw [he,frozenCorner_label]
    cases o <;> rfl
  let z := apexInstanceAt n w d c hc f P select g.1 y hsel hstart
  let x : P.Link z.val := ⟨y,rfl⟩
  have hnot : ¬∃ a e, P.index y = .inl (a,e) := by rw [he]; simp
  have hmark : fragmentMark n w d c hc f P select g.1 z x = .triangle := by
    unfold fragmentMark
    rw [dite_eq_left hsel,dite_eq_right hnot]
  refine ⟨⟨g.1,⟨⟨z,x⟩,hmark⟩⟩,?_⟩
  exact Subtype.ext hface

lemma selectedTriangles_le :
    Fintype.card (SelectedTriangleFace n w d c hc f P select) ≤
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles := by
  rw [← allTriangleIndex_card n w d c hc f P select hs hm hred hrad]
  exact Fintype.card_le_of_surjective _ (triangleFace_surjective n w d c hc f P select hs hm hred hrad)

lemma triangleFace_injective (hb : P.NoBigon) : Function.Injective
    (triangleFace n w d c hc f P select hs hm hred hrad) := by
  intro p q he
  apply triangleRawDart_injective n w d c hc f P select hs hm hred hrad
  have hface := congrArg Subtype.val he
  change P.faceClass p.2.val.2.val = P.faceClass q.2.val.2.val at hface
  have hf : P.faceClass (triangleRawDart n w d c hc f P select hs hm hred hrad p) =
      P.faceClass (triangleRawDart n w d c hc f P select hs hm hred hrad q) := by
    simpa only [triangleRawDart,P.faceClass_apply] using hface
  obtain ⟨g,o,hp⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad p
  obtain ⟨g',o',hq⟩ := triangle_raw_index n w d c hc f P select hs hm hred hrad q
  have hk := congrArg P.faceKind hf
  change walkKind n w d (P.index (triangleRawDart n w d c hc f P select hs hm hred hrad p)) =
    walkKind n w d (P.index (triangleRawDart n w d c hc f P select hs hm hred hrad q)) at hk
  rw [hp,hq] at hk
  have hg : g = g' := Sum.inl.inj (Sum.inr.inj hk)
  apply raw_position_once_per_face n w d c hc f P hs hb hm (P.faceClass_eq.mp hf)
  · rw [hp]; cases o <;> rfl
  · rw [hq]; cases o' <;> rfl
  · rw [hp,hq,hg]; rfl

lemma selectedTriangles_eq (hb : P.NoBigon) :
    Fintype.card (SelectedTriangleFace n w d c hc f P select) =
      ∑ b : Fan n w, (indexedFanData n w d c hc f P select b hs hm hred hrad).triangles := by
  rw [← allTriangleIndex_card n w d c hc f P select hs hm hred hrad]
  exact (Fintype.card_congr (Equiv.ofBijective _
    ⟨triangleFace_injective n w d c hc f P select hs hm hred hrad hb,
     triangleFace_surjective n w d c hc f P select hs hm hred hrad⟩)).symm

end HyperbolicObstruction.ConeSkeleton
end

end OAI
