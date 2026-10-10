import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeMappedWalk
import OAI.Geometry.HyperbolicGroups.WalkRawPosition
import OAI.Geometry.HyperbolicGroups.ConeFanCorner
import OAI.Geometry.HyperbolicGroups.WalkFacePosition

namespace OAI

noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

def exceptionalMacro : MacroGraph.graph.Dart :=
  ⟨(MacroGraph.point 3,MacroGraph.exceptional),rfl⟩

lemma macro_exceptional_port (a : Top n w) (e : MacroGraph.graph.Dart)
    (ha : isApex n w (start n w (macroStep n w a e.adj)) = true)
    (hp : dartPart n w (macroStep n w a e.adj) = false) : e = exceptionalMacro := by
  have ha := (congrArg (isApex n w) (macroStep_start n w a e.adj)).symm.trans ha
  rcases e with ⟨⟨u,v⟩,h⟩
  rcases u with ((i|l)|⟨⟩)
  · rcases v with ((j|m)|⟨⟩)
    · cases h
    · cases hp
    · have hi : i = 3 := h
      subst i
      rfl
  · cases ha
  · cases ha

lemma exceptional_successor (e : MacroGraph.graph.Dart) (hf : e.fst = MacroGraph.exceptional)
    (hn : e ≠ exceptionalMacro.symm) : e = looseMacro := by
  rcases e with ⟨⟨u,v⟩,h⟩
  change u = MacroGraph.exceptional at hf
  subst u
  rcases v with ((i|l)|⟨⟩)
  · have hi : i = 3 := h
    subst i
    exact False.elim (hn rfl)
  · have hl : l = 4 := h
    subst l
    rfl
  · cases h

lemma exceptional_predecessor (e : MacroGraph.graph.Dart) (hf : e.snd = MacroGraph.exceptional)
    (hn : e ≠ exceptionalMacro) : e = looseMacro.symm := by
  have hh := exceptional_successor e.symm hf (fun he => hn (by
    have ht := congrArg SimpleGraph.Dart.symm he
    exact ht))
  exact congrArg SimpleGraph.Dart.symm hh

universe u
variable (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma exceptional_next (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (a,exceptionalMacro)) :
    P.index (P.pairing.face x) = .inl (a,looseMacro) := by
  obtain ⟨e,he⟩ := same_top_face n w d c hc f P hx (SameCycle.rfl.apply_right)
  have hh := P.closed x
  change walkFront n w d (P.index (P.pairing.face x)) = walkBack n w d (P.index x) at hh
  rw [he,hx] at hh
  have hf : e.fst = MacroGraph.exceptional := congrArg Prod.snd (Sum.inl.inj hh)
  have hn : e ≠ exceptionalMacro.symm := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face x) (by rw [hx]; rfl)
      (SameCycle.rfl.apply_right)
    change P.index (P.pairing.face x) = walkOpposite n w d (P.index x)
    rw [he,hx,hh]; rfl
  rw [he,exceptional_successor e hf hn]

lemma exceptional_previous (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (a,exceptionalMacro.symm)) :
    P.index (P.pairing.face⁻¹ x) = .inl (a,looseMacro.symm) := by
  have hxy : P.pairing.face.SameCycle x (P.pairing.face⁻¹ x) :=
    sameCycle_inv.mp (SameCycle.rfl.apply_right)
  obtain ⟨e,he⟩ := same_top_face n w d c hc f P hx hxy
  have hh := P.closed (P.pairing.face⁻¹ x)
  rw [Perm.inv_def,apply_symm_apply] at hh
  change walkFront n w d (P.index x) = walkBack n w d (P.index (P.pairing.face⁻¹ x)) at hh
  rw [he,hx] at hh
  have hf : e.snd = MacroGraph.exceptional := (congrArg Prod.snd (Sum.inl.inj hh)).symm
  have hn : e ≠ exceptionalMacro := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face⁻¹ x) (by rw [hx]; rfl) hxy
    change P.index (P.pairing.face⁻¹ x) = walkOpposite n w d (P.index x)
    rw [he,hx,hh]; rfl
  rw [he,exceptional_predecessor e hf hn]

end HyperbolicObstruction.ConeSkeleton
end

end OAI
