import OAI.RepresentationTheory.FoulkesHowe.Multiplication

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Fixing the first argument and pulling back all other arguments preserves symmetry. -/
theorem symmetric_form_curry_comp {r b m : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V)
    (hT : IsSymmetricMultilinearForm (r+1) b V T)
    (z : SymPow b V) (L : SymPow m V →ₗ[ℂ] SymPow b V) :
    IsSymmetricMultilinearForm r m V ((T.curryLeft z).compLinearMap (fun _ => L)) := by
  intro σ x
  let τ : Equiv.Perm (Fin (r+1)) :=
    (finSuccEquiv r).trans ((Equiv.optionCongr σ).trans (finSuccEquiv r).symm)
  have heq : (fun i : Fin (r+1) => (Fin.cons z (fun j => L (x j)) :
      Fin (r+1) → SymPow b V) (τ i)) =
      (Fin.cons z (fun i => L (x (σ i))) : Fin (r+1) → SymPow b V) := by
    funext i
    cases i using Fin.cases <;> simp [τ]
  simpa only [MultilinearMap.compLinearMap_apply, MultilinearMap.curryLeft_apply, heq]
    using hT τ (Fin.cons z (fun i => L (x i)))

/-- The lower-arity form used in the stabilization induction. -/
def lowerProductForm (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V) :
    SymmetricMultilinearForm r m V :=
  (T.curryLeft (symMonomial (r+m) V (fun _ => t))).compLinearMap
    (fun _ => symPowMul r m (symMonomial r V (fun _ => x)))

@[simp] theorem lowerProductForm_apply (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V)
    (Q : Fin r → SymPow m V) :
    lowerProductForm r m T x t Q =
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) := rfl

theorem lowerProductForm_symmetric (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (hT : IsSymmetricMultilinearForm (r+1) (r+m) V T) (x t : V) :
    IsSymmetricMultilinearForm r m V (lowerProductForm r m T x t) :=
  symmetric_form_curry_comp T hT _ _

end Problem346

end

end OAI
