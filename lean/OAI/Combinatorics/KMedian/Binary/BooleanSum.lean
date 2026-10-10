import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanProducts
import OAI.Combinatorics.KMedian.Binary.BooleanListPrimitives
import OAI.Combinatorics.KMedian.Binary.BooleanRecode

namespace OAI


                                  
section
namespace MetricKMedian.Binary
open Function
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
noncomputable def sumTag : PolyProgram (encodeLoop eb ea) encodeBool Sum.isRight :=
  head.recode (encodeLoop eb ea) (fun _ => rfl) (fun x => by cases x <;> rfl)
noncomputable def sumLeft (a0 : α) : PolyProgram (encodeLoop eb ea) ea (fun x => x.elim id (fun _ => a0)) := by
  let raw := tail.recode (encodeLoop eb ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeLoop eb ea) id (ea a0)
  refine (ite (sumTag ea eb) raw deflt).recode id (fun _ => rfl) ?_
  intro x
  cases x <;> rfl
noncomputable def sumRight (b0 : β) : PolyProgram (encodeLoop eb ea) eb (fun x => x.elim (fun _ => b0) id) := by
  let raw := tail.recode (encodeLoop eb ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeLoop eb ea) id (eb b0)
  refine (ite (sumTag ea eb) deflt raw).recode id (fun _ => rfl) ?_
  intro x
  cases x <;> rfl
noncomputable def sumElim {ec : γ → List Bool} {f : α → γ} {g : β → γ}
    (F : PolyProgram ea ec f) (G : PolyProgram eb ec g) (a0 : α) (b0 : β) :
    PolyProgram (encodeLoop eb ea) ec (Sum.elim f g) :=
  (ite (sumTag ea eb) ((sumLeft ea eb a0).comp F) ((sumRight ea eb b0).comp G)).congr _
    (fun x => by cases x <;> rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
