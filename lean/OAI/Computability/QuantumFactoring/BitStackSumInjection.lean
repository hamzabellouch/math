import Mathlib
import OAI.Computability.QuantumFactoring.BitStackSums
import OAI.Computability.QuantumFactoring.BitStackWords

namespace OAI



section
namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def sumLeft {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure ea (sumCode ea eb) Sum.inl:=
  (prepend ea [false]).result (by intro a;rfl)
noncomputable def sumRight {α β : Type} (ea : α→List Bool) (eb : β→List Bool) :
    Procedure eb (sumCode ea eb) Sum.inr:=
  (prepend eb [true]).result (by intro a;rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
