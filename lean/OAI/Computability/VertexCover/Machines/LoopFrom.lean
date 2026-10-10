import Mathlib
import OAI.Computability.VertexCover.Machines.Lists

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover.Machine
open Turing

noncomputable def Poly.loopFrom {α β : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : Poly e (flagBits e) body) (initial result : β → α) (size count : Polynomial ℕ)
    (spec : ∀ b, ∃ n, n ≤ count.eval (e (initial b)).length ∧
      BoundedRun e body (size.eval (e (initial b)).length) (initial b) (result b) n) :
    Poly (fun b => e (initial b)) e result where
  computation := {
    tm := Loop.machine c.computation.tm c.computation.inputAlphabet c.computation.outputAlphabet
    inputAlphabet := c.computation.inputAlphabet
    outputAlphabet := Equiv.refl Bool
    time := count * (loopCost c.computation).comp size
    outputsFun := fun a => Classical.choice (by
      simp only [show (Equiv.refl Bool).invFun = id from rfl, List.map_id]
      obtain ⟨n, hn, run⟩ := spec a
      obtain ⟨execution⟩ := boundedRun_execution c.computation run
      refine ⟨{ execution with steps_le_m := ?_ }⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_comp]
      exact execution.steps_le_m.trans (Nat.mul_le_mul_right _ hn)) }
  finiteAlphabet := Loop.finiteAlphabet _ _ _ c.finiteAlphabet

noncomputable def Poly.initializeLoop {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {initial : α → β} {result : α → β} (ci : Poly ea eb initial)
    (cl : Poly (fun a => eb (initial a)) eb result) : Poly ea eb result := by
  let first : Poly ea (fun a => eb (initial a)) id := ci.encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact (first.comp cl).congr (fun _ => rfl)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
