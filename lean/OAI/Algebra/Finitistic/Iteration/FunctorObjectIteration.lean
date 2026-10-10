import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.Logic.Function.Iterate

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u v
variable {C : Type u} [Category.{v} C] {F G : C ⥤ C}

/-- An actual natural isomorphism identifies every objectwise iterate. -/
def functorObjectIteration (e : F ≅ G) (r : ℕ) (Y : C) :
    (F.obj^[r]) Y ≅ (G.obj^[r]) Y := by
  induction r with
  | zero => exact Iso.refl _
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact F.mapIso ih ≪≫ e.app _

/-- Transport an object isomorphism through an actual repeated functor. -/
def mapObjectIteration (F : C ⥤ C) {X Y : C} (e : X ≅ Y) (r : ℕ) :
    (F.obj^[r]) X ≅ (F.obj^[r]) Y := by
  induction r with
  | zero => exact e
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact F.mapIso ih
end LittleFinitistic

end

end OAI
