import Mathlib
import OAI.Computability.QuantumFactoring.ControlledTranslation
import OAI.Computability.QuantumFactoring.CleanPermutation

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.ControlledTranslation
open BooleanNetwork

/-- The clean finite-gate controlled-shift implementation derived from its
forward and inverse verified combinational networks. -/
def circuit {p b : ℕ} (δ : BooleanNetwork p b) :
    List (Instruction ((p+b)+(p+b)+(δ.net.count+158*b+6))) :=
  cleanPermutation (forward δ) (backward δ)
    (by have := forward_count δ; omega) (backward_count δ)

lemma circuit_basis {p b : ℕ} (δ : BooleanNetwork p b) (x : Basis (p+b)) :
    (programMatrix (circuit δ)).mulVec
        (basisVector (packed (δ.net.count+158*b+6) x (fun _ => false))) =
      basisVector (packed (δ.net.count+158*b+6)
        (translate (fun d => bitsValue (δ.eval d)) x) (fun _ => false)) := by
  rw [circuit, cleanPermutation_basis _ _ _ _ x (forward_backward δ x), forward_correct]

lemma circuit_length {p b : ℕ} (δ : BooleanNetwork p b) :
    (circuit δ).length ≤ 8*δ.net.count+983*b+7*p+48 := by
  have h := cleanPermutation_length (forward δ) (backward δ)
    (show (forward δ).net.count ≤ δ.net.count+158*b+6 by have := forward_count δ; omega)
    (backward_count δ)
  have hf := forward_count δ
  have hg := backward_count δ
  change (cleanPermutation (forward δ) (backward δ) _ _).length ≤ _
  omega

end ExactQuantumFactoring.ControlledTranslation


end

end OAI
