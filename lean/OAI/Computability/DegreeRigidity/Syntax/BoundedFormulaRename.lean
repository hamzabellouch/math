import OAI.Computability.DegreeRigidity.Effective.FiniteTuple

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

@[simp] theorem Formula.eval_rename_comp (p : Formula) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (p.rename r).Eval e ↔ p.Eval (e ∘ r) := Formula.eval_rename p r e
end TuringRigidity.BoundedSetTheory

end OAI
