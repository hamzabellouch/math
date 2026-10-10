import Mathlib
import OAI.Computability.QuantumFactoring.AIGCompiler
import OAI.Computability.QuantumFactoring.AIGBounds
import OAI.Computability.QuantumFactoring.AIGInputs
import OAI.Computability.QuantumFactoring.BitEncoding

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

/-- The two actual little-endian input words of the bitblaster. -/
def binaryInputs (w : ℕ) : AIG.BinaryRefVec (inputs (w+w)).1 w :=
  ⟨refVector (fun i => (inputs (w+w)).2 (i.castAdd w)),
   refVector (fun i => (inputs (w+w)).2 (Fin.natAdd w i))⟩

def leftWord {w : ℕ} (x : Fin (w+w) → Bool) : BitVec w :=
  bitsValue (fun i => x (i.castAdd w))
def rightWord {w : ℕ} (x : Fin (w+w) → Bool) : BitVec w :=
  bitsValue (fun i => x (Fin.natAdd w i))

lemma binaryInputs_left (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).lhs.get i hi⟩ =
      (leftWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (j.castAdd w)) ⟨i,hi⟩).symm

lemma binaryInputs_right (w : ℕ) (x : Fin (w+w) → Bool) (i : ℕ) (hi : i < w) :
    AIG.denote x ⟨(inputs (w+w)).1, (binaryInputs w).rhs.get i hi⟩ =
      (rightWord x).getLsbD i := by
  rw [binaryInputs, refVector_get, inputs_correct]
  exact (bitsValue_bit (fun j => x (Fin.natAdd w j)) ⟨i,hi⟩).symm

def add (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastAdd (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma add_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (add w).eval x i = (leftWord x + rightWord x).getLsbD i.val := by
  rw [add, compileVec_correct]
  exact denote_blastAdd _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

def mul (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastMul (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma mul_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mul w).eval x i = (leftWord x * rightWord x).getLsbD i.val := by
  rw [mul, compileVec_correct]
  exact denote_blastMul _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma add_count (w : ℕ) : (add w).net.count ≤ 86*w+6 := by
  have h := compileVec_count (blastAdd (inputs (w+w)).1 (binaryInputs w)).aig
    (blastAdd (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.add_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [add]
  omega

lemma mul_count (w : ℕ) : (mul w).net.count ≤ 90*w*w+14*w+6 := by
  have h := compileVec_count (blastMul (inputs (w+w)).1 (binaryInputs w)).aig
    (blastMul (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.mul_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [mul]
  nlinarith

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
