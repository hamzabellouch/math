import Mathlib
import OAI.Computability.QuantumFactoring.RegisterBasis
import OAI.Computability.QuantumFactoring.EncodedStates

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma Register.replace_injective {p q : ℕ} (w : Register p q) (x : Basis q) :
    Function.Injective (w.replace x) := by
  intro u v h
  funext i
  have hh := congrFun h (w i)
  simpa only [Register.replace_inside] using hh

lemma Register.placed_basis_state {p q : ℕ} (w : Register p q)
    (ops : List (Instruction p)) (x : Basis q) :
    (programMatrix (ops.map (Instruction.place w))).mulVec (basisVector x) =
      encodeState (w.replace x) ((programMatrix ops).mulVec (basisVector (x ∘ w))) := by
  classical
  rw [programMatrix_place, ← w.pairState_basis x, w.liftMatrix_pairState]
  unfold encodeState
  simp_rw [← w.pairState_replace_basis]
  funext y
  simp only [Register.pairState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    basisVector]
  simp

end ExactQuantumFactoring


end

end OAI
