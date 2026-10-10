import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeFrozenTarget

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open Equiv Equiv.Perm
variable {C L V : Type*} (B : Boundary C L V)
lemma side_sameCycle (c : C) (o : Bool) (i j : Fin (B.size c)) :
    B.next.SameCycle ⟨c,o,i⟩ ⟨c,o,j⟩ := by
  have hr : (finRotate (B.size c)).SameCycle i j := by
    by_cases hh : 2 ≤ B.size c
    · apply (isCycle_finRotate_of_le hh).sameCycle
      · exact mem_support.mp (by rw [support_finRotate_of_le hh]; exact Finset.mem_univ i)
      · exact mem_support.mp (by rw [support_finRotate_of_le hh]; exact Finset.mem_univ j)
    · have hij : i = j := Fin.ext (by omega)
      exact hij.sameCycle _
  cases o
  · apply sameCycle_inv.mp
    apply semiconj_perm_sameCycle (f := finRotate (B.size c))
      (j := fun i => (⟨c,false,i⟩ : B.Side)) _ hr
    intro i
    rfl
  · apply semiconj_perm_sameCycle (f := finRotate (B.size c))
      (j := fun i => (⟨c,true,i⟩ : B.Side)) _ hr
    intro i
    rfl
end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary

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

lemma frozen_side_exists (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {k : FrozenCell n w d} {o : Bool} {i : Fin ((frozenBoundary n w d).size k)}
    (hx : P.index x = .inr ⟨k,o,i⟩) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ y, P.pairing.face.SameCycle x y ∧ P.index y = .inr ⟨k,o,j⟩ := by
  let x' : P.FrozenDart := ⟨x,by rw [hx]; rfl⟩
  have hh : (walkFrozenTarget n w d c hc f).next.SameCycle (P.index x) (.inr ⟨k,o,j⟩) := by
    rw [hx]
    apply semiconj_perm_sameCycle (f := (frozenBoundary n w d).next)
      (j := Sum.inr) (fun s => rfl) ((frozenBoundary n w d).side_sameCycle k o i j)
  obtain ⟨y,hy,he⟩ := hm.orbit_surjective x' hh
  exact ⟨y.val,sameCycle_subtypePerm.mp hy,he⟩

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
