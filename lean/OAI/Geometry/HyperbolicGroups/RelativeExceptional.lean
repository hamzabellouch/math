import Mathlib
import OAI.Geometry.HyperbolicGroups.MacroExceptional
import OAI.Geometry.HyperbolicGroups.RelativeApexLocal

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma exceptional_next (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (.inl (a,exceptionalMacro))) :
    P.index (P.pairing.face x) = .inl (.inl (a,looseMacro)) := by
  obtain ⟨e,he⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx (SameCycle.rfl.apply_right)
  have hh := P.closed x
  change (target n w d ell hell word c hc f).front (P.index (P.pairing.face x)) = (target n w d ell hell word c hc f).back (P.index x) at hh
  rw [he,hx] at hh
  have hf : e.fst = MacroGraph.exceptional := congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj hh))
  have hn : e ≠ exceptionalMacro.symm := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face x) (by rw [hx]; rfl)
      (SameCycle.rfl.apply_right)
    rw [he,hx,hh]; rfl
  rw [he,exceptional_successor e hf hn]

lemma exceptional_previous (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (.inl (a,exceptionalMacro.symm))) :
    P.index (P.pairing.face⁻¹ x) = .inl (.inl (a,looseMacro.symm)) := by
  have hxy : P.pairing.face.SameCycle x (P.pairing.face⁻¹ x) :=
    sameCycle_inv.mp (SameCycle.rfl.apply_right)
  obtain ⟨e,he⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx hxy
  have hh := P.closed (P.pairing.face⁻¹ x)
  rw [Perm.inv_def,apply_symm_apply] at hh
  change (target n w d ell hell word c hc f).front (P.index x) = (target n w d ell hell word c hc f).back (P.index (P.pairing.face⁻¹ x)) at hh
  rw [he,hx] at hh
  have hf : e.snd = MacroGraph.exceptional := (congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj hh))).symm
  have hn : e ≠ exceptionalMacro := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face⁻¹ x) (by rw [hx]; rfl) hxy
    rw [he,hx,hh]; rfl
  rw [he,exceptional_predecessor e hf hn]

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
