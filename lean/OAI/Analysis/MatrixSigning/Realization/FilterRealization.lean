import Mathlib
import OAI.Analysis.MatrixSigning.Realization.StoredPSDRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

def Realizes.flatMap {ea : α → Word} {eb : β → Word} {f : α → List β}
    (r : Realizes ea (listCode eb) f) : Realizes (listCode ea) (listCode eb) (List.flatMap f) :=
  (r.map.then (joinList eb)).congr (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
