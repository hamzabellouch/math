import Mathlib
import OAI.Combinatorics.KMedian.PCP.AlphabetReduction

namespace OAI

section Inline_PCPVertexMap
namespace MetricKMedian.PCP.BinaryCSP
open scoped Classical

variable {V W E A : Type} [Fintype E] [DecidableEq A]
variable (C : BinaryCSP V E A) (e : V ↪ W)
def mapVertices : BinaryCSP W E A where
  left t := e (C.left t)
  right t := e (C.right t)
  allowed := C.allowed
omit [DecidableEq A]
lemma mapVertices_rejection (a : W → A) :
    (C.mapVertices e).rejection a=C.rejection (a ∘ e) := rfl
noncomputable def extendAssignment [Inhabited A] (a : V → A) (w : W) : A :=
  if h : w∈Set.range e then a (Classical.choose h) else default
@[simp] lemma extendAssignment_image [Inhabited A] (a : V → A) (v : V) :
    extendAssignment e a (e v)=a v := by
  simp only [extendAssignment,Set.mem_range_self,↓reduceDIte]
  exact congrArg a (e.injective (Classical.choose_spec (Set.mem_range_self v)))
omit [Fintype E] in
lemma mapVertices_complete [Inhabited A] (a : V → A) (ha : C.Satisfies a) :
    (C.mapVertices e).Satisfies (extendAssignment e a) := by
  intro t
  simpa only [mapVertices,extendAssignment_image] using ha t
end MetricKMedian.PCP.BinaryCSP

end Inline_PCPVertexMap

end OAI
