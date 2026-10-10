import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFanIncoming
import OAI.Geometry.HyperbolicGroups.WalkConeLink
import OAI.Geometry.HyperbolicGroups.FanApex
import OAI.Geometry.HyperbolicGroups.WalkClasses

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool) (b : Fan n w)

lemma macroVertex_fan_slot (a : Top n w) (v : MacroGraph.Vertex)
    (h : macroVertex n w a v = .inr b) : ∃ i, slot n w a i = b := by
  rcases v with ((i|l)|⟨⟩)
  · exact ⟨i,Sum.inr.inj h⟩
  · cases h
  · cases h

/-- ALL selected top polygons incident to this fan occurrence, not only those
whose boundary actually visits it. -/
abbrev SelectedTop := {z : P.Face // select z = true ∧ ∃ a : Top n w,
  P.faceKind z = .inl a ∧ ∃ i, slot n w a i = b}

/-- Actual source vertices over this fan, represented in the chosen fragment. -/
abbrev ApexInstance := {z : P.Vertex //
  start n w (walkLabel n w d (P.index z.out)) = .inr b ∧
    ∃ x, P.vertexClass x = z ∧ select (P.faceClass x) = true}

noncomputable instance : Fintype (SelectedTop n w d c hc f P select b) := Fintype.ofFinite _
noncomputable instance : Fintype (ApexInstance n w d c hc f P select b) := Fintype.ofFinite _

def selectedOccurrence (F : SelectedTop n w d c hc f P select b) : Top n w :=
  F.property.2.choose

lemma selectedOccurrence_kind (F : SelectedTop n w d c hc f P select b) :
    P.faceKind F.val = .inl (selectedOccurrence n w d c hc f P select b F) :=
  F.property.2.choose_spec.1

lemma instance_start (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    start n w (walkLabel n w d (P.index x.val)) = .inr b := by
  have hh : P.pairing.vertex.SameCycle z.val.out x.val :=
    P.vertexClass_eq.mp ((P.vertexClass_out _).trans x.property.symm)
  exact (walk_start_link_constant n w d c hc f P hh).symm.trans z.property.1

lemma instance_apex (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    isApex n w (start n w (walkLabel n w d (P.index x.val))) = true := by
  rw [instance_start n w d c hc f P select b z x]; rfl

def selectedTopAt (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (hs : select (P.faceClass x.val) = true)
    (ht : ∃ a e, P.index x.val = .inl (a,e)) : SelectedTop n w d c hc f P select b := by
  refine ⟨P.faceClass x.val,hs,?_⟩
  obtain ⟨a,e,hx⟩ := ht
  refine ⟨a,?_,?_⟩
  · change walkKind n w d (P.index x.val) = .inl a
    rw [hx]; rfl
  · apply macroVertex_fan_slot n w b a e.fst
    have hh := instance_start n w d c hc f P select b z x
    rw [hx] at hh
    exact (macroStep_start n w a e.adj).symm.trans hh

def fragmentMark (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    FanLink.Mark (SelectedTop n w d c hc f P select b) :=
  if hs : select (P.faceClass x.val) = true then
    if ht : ∃ a e, P.index x.val = .inl (a,e) then
      .top (selectedTopAt n w d c hc f P select b z x hs ht)
    else .triangle
  else .absent

lemma mark_absent (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    fragmentMark n w d c hc f P select b z x = .absent ↔ select (P.faceClass x.val) ≠ true := by
  unfold fragmentMark
  split_ifs <;> simp_all

lemma mark_top_face (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (F : SelectedTop n w d c hc f P select b)
    (h : fragmentMark n w d c hc f P select b z x = .top F) :
    F.val = P.faceClass x.val := by
  unfold fragmentMark at h
  split_ifs at h with hs ht
  exact congrArg Subtype.val (FanLink.Mark.top.inj h).symm

lemma mark_top_index (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (F : SelectedTop n w d c hc f P select b)
    (h : fragmentMark n w d c hc f P select b z x = .top F) :
    ∃ e, P.index x.val = .inl (selectedOccurrence n w d c hc f P select b F,e) := by
  have hk := selectedOccurrence_kind n w d c hc f P select b F
  rw [mark_top_face n w d c hc f P select b z x F h] at hk
  change walkKind n w d (P.index x.val) = .inl _ at hk
  cases hx : P.index x.val with
  | inl s =>
    rw [hx] at hk
    change Sum.inl s.1 = Sum.inl _ at hk
    exact ⟨s.2,congrArg Sum.inl (Prod.ext (Sum.inl.inj hk) rfl)⟩
  | inr s => rw [hx] at hk; cases hk

lemma mark_triangle_corner (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (h : fragmentMark n w d c hc f P select b z x = .triangle) :
    ∃ g o, P.index x.val = frozenCorner n w d g o := by
  rcases walk_apex_cases n w d c hc f P x.val
    (instance_apex n w d c hc f P select b z x) with ⟨a,e,hx⟩ | hh
  · have ht : ∃ a e, P.index x.val = .inl (a,e) := ⟨a,e,hx⟩
    unfold fragmentMark at h
    split_ifs at h with hs
  · exact hh

lemma fragment_represented (z : ApexInstance n w d c hc f P select b) :
    ∃ x, fragmentMark n w d c hc f P select b z x ≠ .absent := by
  obtain ⟨x,hx,hs⟩ := z.property.2
  exact ⟨⟨x,hx⟩,fun h => (mark_absent n w d c hc f P select b z ⟨x,hx⟩).mp h hs⟩

lemma fragment_card (hrad : P.RadialInjective (isApex n w))
    (z : ApexInstance n w d c hc f P select b) : Fintype.card (P.Link z.val) ≤ 5 := by
  rw [P.link_card]
  exact walk_link_card n w d c hc f P hrad z.val.out b z.property.1

lemma fragment_no_fixed (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    P.linkNext z.val x ≠ x := by
  intro he
  have he' := congrArg Subtype.val he
  change P.pairing.vertex⁻¹ x.val = x.val at he'
  have hh := congrArg P.pairing.vertex he'
  simp only [Perm.inv_def,apply_symm_apply] at hh
  exact walk_apex_no_fixed n w d c hc f P hm hred x.val
    (instance_apex n w d c hc f P select b z x) hh.symm

lemma fragment_bipartite (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (h : fragmentMark n w d c hc f P select b z x = .triangle) :
    dartPart n w (walkLabel n w d (P.index x.val)) ≠
      dartPart n w (walkLabel n w d (P.index (P.linkNext z.val x).val)) := by
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d c hc f P select b z x h
  exact walk_triangle_bipartite n w d c hc f P hm hx

lemma fragment_no_backtrack (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (hx : fragmentMark n w d c hc f P select b z x = .triangle)
    (hy : fragmentMark n w d c hc f P select b z (P.linkNext z.val x) = .triangle) :
    P.linkNext z.val (P.linkNext z.val x) ≠ x := by
  obtain ⟨g,o,hg⟩ := mark_triangle_corner n w d c hc f P select b z x hx
  obtain ⟨h,p,hh⟩ := mark_triangle_corner n w d c hc f P select b z (P.linkNext z.val x) hy
  intro he
  exact walk_triangle_inverse_no_two n w d c hc f P hm hred hg hh (congrArg Subtype.val he)

lemma fragment_no_same_side (hred : P.FullyReduced)
    (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (F G : SelectedTop n w d c hc f P select b)
    (hx : fragmentMark n w d c hc f P select b z x = .top F)
    (hy : fragmentMark n w d c hc f P select b z (P.linkNext z.val x) = .top G) :
    selectedOccurrence n w d c hc f P select b F ≠ selectedOccurrence n w d c hc f P select b G := by
  obtain ⟨e,he⟩ := mark_top_index n w d c hc f P select b z x F hx
  obtain ⟨k,hk⟩ := mark_top_index n w d c hc f P select b z (P.linkNext z.val x) G hy
  exact Ne.symm (walk_top_adjacent_different n w d c hc f P hred hk
    (by simpa only [P.linkNext_val,Perm.inv_def,apply_symm_apply] using he)
    (instance_apex n w d c hc f P select b z (P.linkNext z.val x)))

lemma fragment_unique_turn (hs : P.Simple)
    (p q : Σ z : ApexInstance n w d c hc f P select b, P.Link z.val)
    (F : SelectedTop n w d c hc f P select b)
    (hp : fragmentMark n w d c hc f P select b p.1 p.2 = .top F)
    (hq : fragmentMark n w d c hc f P select b q.1 q.2 = .top F) : p = q := by
  obtain ⟨e,he⟩ := mark_top_index n w d c hc f P select b p.1 p.2 F hp
  have hface := (mark_top_face n w d c hc f P select b p.1 p.2 F hp).symm.trans
    (mark_top_face n w d c hc f P select b q.1 q.2 F hq)
  have hd := walk_top_unique_turn n w d c hc f P hs he (P.faceClass_eq.mp hface) b
    (instance_start n w d c hc f P select b p.1 p.2)
    (instance_start n w d c hc f P select b q.1 q.2)
  have hz : p.1 = q.1 := Subtype.ext (p.2.property.symm.trans
    ((congrArg P.vertexClass hd).trans q.2.property))
  rcases p with ⟨z,x⟩; rcases q with ⟨y,k⟩
  dsimp at hz hd
  subst y
  exact congrArg (Sigma.mk z) (Subtype.ext hd)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
