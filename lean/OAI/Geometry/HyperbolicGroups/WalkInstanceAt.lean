import Mathlib
import OAI.Geometry.HyperbolicGroups.WalkFragment

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
variable (select : P.Face → Bool)

def apexInstanceAt (b : Fan n w) (x : P.Dart)
    (hs : select (P.faceClass x) = true)
    (hx : start n w (walkLabel n w d (P.index x)) = .inr b) :
    ApexInstance n w d c hc f P select b :=
  ⟨P.vertexClass x,by
    have hh : P.pairing.vertex.SameCycle (P.vertexClass x).out x :=
      P.vertexClass_eq.mp (P.vertexClass_out _)
    exact (walk_start_link_constant n w d c hc f P hh).trans hx,
    x,rfl,hs⟩


end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
