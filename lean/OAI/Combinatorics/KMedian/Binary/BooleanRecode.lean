import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanPolynomial

namespace OAI


                                     
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β α' β' : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {ea' : α' → List Bool} {eb' : β' → List Bool} {f : α → β} {f' : α' → β'}

def recode (P : PolyProgram ea eb f) (i : α' → α)
    (hi : ∀ a, ea (i a)=ea' a) (ho : ∀ a, eb (f (i a))=eb' (f' a)) :
    PolyProgram ea' eb' f' where
  machine := P.machine
  time := P.time
  outputs a := by
    have h := P.outputs (i a)
    rwa [hi,ho] at h

end MetricKMedian.Binary.PolyProgram
end

end OAI
