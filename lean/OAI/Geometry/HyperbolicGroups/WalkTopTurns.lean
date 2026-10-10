import Mathlib
import OAI.Geometry.HyperbolicGroups.FragmentSlots

namespace OAI

section
section


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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

/-- Actual source-face cardinal bound, not an assumed macro polygon. -/
lemma top_face_apex_card_ge (hs : P.Simple) (hb : P.NoBigon)
    (x : P.Dart) (a : Top n w) (e : MacroGraph.graph.Dart) (hx : P.index x = .inl (a,e)) :
    3 ≤ Fintype.card {y : P.Dart // P.pairing.face.SameCycle x y ∧
      isApex n w (start n w (walkLabel n w d (P.index y))) = true} := by
  let I := {y : P.Dart // P.pairing.face.SameCycle x y}
  let R := mappedMacroPolygon n w d c hc f P hs hb x a e hx
  let b : Fin R.n ≃ I := (Fintype.equivFin I).symm
  let j (y : I) : MacroGraph.graph.Dart := (same_top_face n w d c hc f P hx y.property).choose
  have hj (y : I) : P.index y.val = .inl (a,j y) :=
    (same_top_face n w d c hc f P hx y.property).choose_spec
  have hv (i : Fin R.n) : R.vertex i = (j (b i)).fst := rfl
  let : Nonempty I := ⟨⟨x,SameCycle.rfl⟩⟩
  have hn : 0 < R.n := Fintype.card_pos
  have hp := R.points_ge hn
  have hex (p : {p : Fin 7 // p ∈ R.points}) : ∃ i : Fin R.n, R.vertex i = MacroGraph.point p.val := by
    have hmem : MacroGraph.point p.val ∈ R.vertices := (Finset.mem_filter.mp p.property).2
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
    exact ⟨i,hi⟩
  let choose (p : {p : Fin 7 // p ∈ R.points}) : Fin R.n := (hex p).choose
  have hchoose (p : {p : Fin 7 // p ∈ R.points}) : (j (b (choose p))).fst = MacroGraph.point p.val := by
    exact (hv _).symm.trans (hex p).choose_spec
  let g : {p : Fin 7 // p ∈ R.points} → {y : P.Dart // P.pairing.face.SameCycle x y ∧
      isApex n w (start n w (walkLabel n w d (P.index y))) = true} := fun p =>
    ⟨(b (choose p)).val,(b (choose p)).property,by
      rw [hj]
      change isApex n w (start n w (macroStep n w a (show MacroGraph.Adjacent _ _ from (j (b (choose p))).adj))) = true
      rw [macroStep_start,hchoose]
      rfl⟩
  have hg : Function.Injective g := by
    intro p q he
    have hh := congrArg Subtype.val he
    change (b (choose p)).val = (b (choose q)).val at hh
    have hb : b (choose p) = b (choose q) := Subtype.ext hh
    have hpp : MacroGraph.point p.val = MacroGraph.point q.val :=
      (hchoose p).symm.trans ((congrArg (fun y => (j y).fst) hb).trans (hchoose q))
    exact Subtype.ext (Sum.inl.inj (Sum.inl.inj hpp))
  have hcard := Fintype.card_le_of_injective g hg
  exact hp.trans (by simpa only [Fintype.card_coe] using hcard)

variable (select : P.Face → Bool)
abbrev TopTurnDart := {x : P.Dart // select (P.faceClass x) = true ∧
  isApex n w (start n w (walkLabel n w d (P.index x))) = true ∧
  walkFree n w d (walkKind n w d (P.index x)) = true}
noncomputable instance : Fintype (TopTurnDart n w d c hc f P select) := Fintype.ofFinite _

abbrev FaceApexDart (F : SelectedTopFace n w d c hc f P select) :=
  {x : P.Dart // P.faceClass x = F.val ∧ isApex n w (start n w (walkLabel n w d (P.index x))) = true}
noncomputable instance (F : SelectedTopFace n w d c hc f P select) :
    Fintype (FaceApexDart n w d c hc f P select F) := Fintype.ofFinite _

lemma face_apex_card_ge (hs : P.Simple) (hb : P.NoBigon)
    (F : SelectedTopFace n w d c hc f P select) :
    3 ≤ Fintype.card (FaceApexDart n w d c hc f P select F) := by
  obtain ⟨a,ha⟩ := F.property.2
  have hk : walkKind n w d (P.index F.val.out) = .inl a := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [P.faceClass_out]; exact ha
  obtain ⟨e,he⟩ : ∃ e, P.index F.val.out = .inl (a,e) := by
    cases ht : P.index F.val.out with
    | inl s =>
      rw [ht] at hk
      exact ⟨s.2,congrArg Sum.inl (Prod.ext (Sum.inl.inj hk) rfl)⟩
    | inr s => rw [ht] at hk; cases hk
  have h := top_face_apex_card_ge n w d c hc f P hs hb F.val.out a e he
  convert h using 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [← P.faceClass_eq,P.faceClass_out]
  exact and_congr eq_comm Iff.rfl

/-- The bound `sum d_z >= 3 T` at the actual selected top faces. The following
apex transport identifies these darts with the indexed fan-turn counts. -/
lemma selected_top_turns_ge (hs : P.Simple) (hb : P.NoBigon) :
    3 * Fintype.card (SelectedTopFace n w d c hc f P select) ≤
      Fintype.card (TopTurnDart n w d c hc f P select) := by
  let I := Σ F : SelectedTopFace n w d c hc f P select, FaceApexDart n w d c hc f P select F
  let g : I → TopTurnDart n w d c hc f P select := fun p => ⟨p.2.val,by
    refine ⟨?_,p.2.property.2,?_⟩
    · rw [p.2.property.1]; exact p.1.property.1
    · have hk : walkKind n w d (P.index p.2.val) = .inl (faceOccurrence n w d c hc f P select p.1) := by
        change P.faceKind (P.faceClass p.2.val) = _
        rw [p.2.property.1]; exact faceOccurrence_kind n w d c hc f P select p.1
      rw [hk]; rfl⟩
  have hg : Function.Injective g := by
    rintro ⟨F,x⟩ ⟨G,y⟩ h
    have hv : x.val = y.val := congrArg Subtype.val h
    have hf : F = G := Subtype.ext (x.property.1.symm.trans ((congrArg P.faceClass hv).trans y.property.1))
    subst G
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun F _ => face_apex_card_ge n w d c hc f P select hs hb F)
  have hh' : 3 * Fintype.card (SelectedTopFace n w d c hc f P select) ≤ Fintype.card I := by
    rw [Fintype.card_sigma]
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.mul_comm] using hh
  exact hh'.trans (Fintype.card_le_of_injective g hg)

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
