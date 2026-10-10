import Mathlib
import OAI.Geometry.HyperbolicGroups.FrozenSideExists
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

lemma frozen_side_exists (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {k : FrozenCell n w d} {o : Bool} {i : Fin ((frozenBoundary n w d).size k)}
    (hx : P.index x = .inl (.inr ⟨k,o,i⟩)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ y, P.pairing.face.SameCycle x y ∧ P.index y = .inl (.inr ⟨k,o,j⟩) := by
  let x' : P.FrozenDart := ⟨x,by rw [hx]; rfl⟩
  have hh : (frozen n w d ell hell word c hc f).next.SameCycle (P.index x) (.inl (.inr ⟨k,o,j⟩)) := by
    rw [hx]
    apply semiconj_perm_sameCycle (f := (frozenBoundary n w d).next)
      (j := Sum.inl ∘ Sum.inr) (fun s => rfl) ((frozenBoundary n w d).side_sameCycle k o i j)
  obtain ⟨y,hy,he⟩ := hm.orbit_surjective x' hh
  exact ⟨y.val,sameCycle_subtypePerm.mp hy,he⟩

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
