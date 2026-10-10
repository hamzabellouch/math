import Mathlib
import OAI.Geometry.HyperbolicGroups.ConeGraph
import OAI.Geometry.HyperbolicGroups.MacroWalk

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

/-- Read only the indexed radial port, not its numerical letter assignment,
back into the subdivided macro template. -/
def radialTemplate : Dart n w → Option (MacroGraph.Vertex × MacroGraph.Vertex)
  | (.inl _,_) => none
  | (.inr ⟨b,v⟩,true) => some (MacroGraph.point b.val.1,
      match v.val with | .inl _ => .inr () | .inr l => .inl (.inr l))
  | (.inr _,false) => none

lemma macroStep_radialTemplate (a : Top n w) (e : MacroGraph.graph.Dart)
    (ha : isApex n w (start n w (macroStep n w a e.adj)) = true) :
    radialTemplate n w (macroStep n w a e.adj) = some e.toProd := by
  rcases e with ⟨⟨u,v⟩,h⟩
  change MacroGraph.Adjacent u v at h
  change isApex n w (start n w (macroStep n w a h)) = true at ha
  change radialTemplate n w (macroStep n w a h) = some (u,v)
  rw [macroStep_start] at ha
  rcases u with ((i|l)|⟨⟩)
  · rcases v with ((j|m)|⟨⟩)
    · exact h.elim
    · rfl
    · have hi : i = 3 := h; subst i; rfl
  · cases ha
  · cases ha

lemma macroStep_radial_injective (a : Top n w) (e k : MacroGraph.graph.Dart)
    (ha : isApex n w (start n w (macroStep n w a e.adj)) = true)
    (h : macroStep n w a e.adj = macroStep n w a k.adj) : e = k := by
  have hb : isApex n w (start n w (macroStep n w a k.adj)) = true := by rw [← h]; exact ha
  have hh := congrArg (radialTemplate n w) h
  rw [macroStep_radialTemplate n w a e ha,macroStep_radialTemplate n w a k hb] at hh
  exact SimpleGraph.Dart.ext e k (Option.some.inj hh)

lemma macroVertex_at_apex (a : Top n w) (u : MacroGraph.Vertex) (b : Fan n w)
    (h : macroVertex n w a u = .inr b) : u = MacroGraph.point b.val.1 := by
  rcases u with ((i|l)|⟨⟩)
  · have hb : slot n w a i = b := Sum.inr.inj h
    have hi := congrArg (fun b : Fan n w => b.val.1) hb
    exact congrArg MacroGraph.point hi
  · cases h
  · cases h

end HyperbolicObstruction.ConeSkeleton
end
end

section

end
end

end OAI
