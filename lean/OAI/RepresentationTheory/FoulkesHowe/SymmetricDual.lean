import OAI.RepresentationTheory.FoulkesHowe.Model
import OAI.RepresentationTheory.FoulkesHowe.AlgebraEvaluation

namespace OAI

noncomputable section
universe u
namespace Problem346

variable (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A symmetric-power duality map is injective as soon as evaluation on pure powers agrees
with evaluation in the symmetric algebra. -/
theorem symPowDual_injective_of_pure_evaluation (n : ℕ)
    (B : SymPow n (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (SymPow n V))
    (hB : ∀ (p : SymPow n (Module.Dual ℂ V)) (x : V),
      B p (symMonomial n V (fun _ => x)) =
        SymmetricAlgebra.lift (Module.Dual.eval ℂ V x) p.val) :
    Function.Injective B := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply symAlg_dual_eq_zero_of_eval_eq_zero V
  intro x
  rw [map_sub, ← hB p x, ← hB q x, hpq, sub_self]

end Problem346

end

end OAI
