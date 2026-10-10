import Mathlib
import OAI.Computability.QuantumFactoring.BooleanAlgebra
import OAI.Computability.QuantumFactoring.EncodedStates
import OAI.Computability.QuantumFactoring.OracleLayout
import OAI.Computability.QuantumFactoring.PhasePreparation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

lemma phase_twice_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (programMatrix [phaseAt t,phaseAt t]).mulVec (basisVector x) =
      (if x t then (-1:ℂ) else 1) • basisVector x := by
  classical
  rw [programMatrix_cons, programMatrix_singleton, ← Matrix.mulVec_mulVec]
  funext y
  rw [phaseAt_apply, phaseAt_apply]
  simp only [Pi.smul_apply, smul_eq_mul, basisVector]
  by_cases h : y=x
  · subst y
    cases x t <;> simp [Complex.I_mul_I]
  · simp [h]

namespace BooleanNetwork

def phaseTarget {n r : ℕ} : Fin (n+1+r) := ⟨n,by omega⟩

/-- Predicate phase kickback is a clean oracle, two S gates, and the same
clean XOR oracle again, all over the fixed gate alphabet. -/
def phaseOracle {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r) :
    List (Instruction (n+1+r)) :=
  oracleOn c hr ++ [phaseAt phaseTarget,phaseAt phaseTarget] ++ oracleOn c hr

lemma phaseOracle_length {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r) :
    (phaseOracle c hr).length ≤ 8*c.net.count+6 := by
  have h := oracleOn_length c hr
  simp only [phaseOracle, List.length_append, List.length_cons, List.length_nil]
  omega

lemma phaseOracle_basis {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r)
    (x : Basis n) :
    (programMatrix (phaseOracle c hr)).mulVec (basisVector (packed r x (fun _ => false))) =
      (if c.eval x 0 then (-1:ℂ) else 1) • basisVector (packed r x (fun _ => false)) := by
  rw [phaseOracle, programMatrix_append, programMatrix_append,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, oracleOn_basis]
  simp only [Bool.false_xor]
  rw [phase_twice_basis, Matrix.mulVec_smul, oracleOn_basis]
  have ht : packed r x (c.eval x) phaseTarget = c.eval x 0 := by
    exact packed_target x (c.eval x) 0
  rw [ht]
  congr 1
  funext i
  simp

/-- The same actual program applies its diagonal predicate phase coherently,
not just on classical basis inputs. -/
lemma phaseOracle_state {n r : ℕ} (c : BooleanNetwork n 1) (hr : c.net.count ≤ r)
    (ψ : Basis n → ℂ) :
    (programMatrix (phaseOracle c hr)).mulVec
      (encodeState (fun x => packed r x (fun _ : Fin 1 => false)) ψ) =
      encodeState (fun x => packed r x (fun _ : Fin 1 => false))
        (fun x => (if c.eval x 0 then (-1:ℂ) else 1)*ψ x) := by
  classical
  rw [encodeState, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, phaseOracle_basis, smul_smul]
  unfold encodeState
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

/-- Bounded fan-in conjunction, built incrementally, not an unbounded gate. -/
def allZero (n : ℕ) : (k : ℕ) → k ≤ n → BooleanNetwork n 1
  | 0, _ => constant true
  | k+1, h => (allZero n k (by omega)).band (bit ⟨k,by omega⟩).bnot

lemma allZero_count (n k : ℕ) (hk : k ≤ n) :
    (allZero n k hk).net.count = 2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [allZero, ih]; omega

lemma allZero_eval (n k : ℕ) (hk : k ≤ n) (x : Basis n) :
    (allZero n k hk).eval x 0 = true ↔ ∀ i : Fin n, i.val < k → x i = false := by
  induction k with
  | zero => simp [allZero]
  | succ k ih =>
    simp only [allZero, eval_band, eval_bnot, eval_bit, Bool.and_eq_true,
      Bool.not_eq_true', ih (by omega)]
    constructor
    · rintro ⟨h₁,h₂⟩ i hi
      by_cases he : i.val=k
      · have hh : i = (⟨k,by omega⟩ : Fin n) := Fin.ext he
        simpa only [hh] using h₂
      · exact h₁ i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h ⟨k,by omega⟩ (by simp)⟩

lemma allZero_full (n : ℕ) (x : Basis n) :
    (allZero n n le_rfl).eval x 0 = true ↔ x = (fun _ => false) := by
  rw [allZero_eval]
  constructor
  · intro h; funext i; exact h i i.isLt
  · rintro rfl; simp

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
