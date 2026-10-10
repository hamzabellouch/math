import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryListMap

namespace OAI


                                          
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
noncomputable def listMapTotal (P : PolyProgram ea eb f) :
    PolyProgram (encodeList ea) (encodeList eb) (List.map f) := by
  classical
  by_cases h : Nonempty α
  · exact P.listMap h.some
  · exact (constant (encodeList ea) (encodeList eb) []).congr _ (by
      intro xs
      cases xs with
      | nil => rfl
      | cons a xs => exact False.elim (h ⟨a⟩))
end MetricKMedian.Binary.PolyProgram
end

end OAI
