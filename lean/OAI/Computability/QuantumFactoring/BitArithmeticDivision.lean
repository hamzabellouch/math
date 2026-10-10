import Mathlib
import OAI.Computability.QuantumFactoring.BitArithmetic
import OAI.Computability.QuantumFactoring.AIGDivisionBounds

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

def sub (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastSub (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma sub_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (sub w).eval x i = (leftWord x - rightWord x).getLsbD i.val := by
  rw [sub, compileVec_correct]
  exact denote_blastSub _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma sub_count (w : ℕ) : (sub w).net.count ≤ 158*w+6 := by
  have h := compileVec_count (blastSub (inputs (w+w)).1 (binaryInputs w)).aig
    (blastSub (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.sub_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [sub]
  nlinarith

def div (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastUdiv (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma div_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (div w).eval x i = (leftWord x / rightWord x).getLsbD i.val := by
  rw [div, compileVec_correct]
  exact denote_blastUdiv _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma div_count (w : ℕ) : (div w).net.count ≤ 216*w*w+56*w+6 := by
  have h := compileVec_count (blastUdiv (inputs (w+w)).1 (binaryInputs w)).aig
    (blastUdiv (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.div_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [div]
  nlinarith

def mod (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastUmod (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma mod_correct (w : ℕ) (x : Fin (w+w) → Bool) (i : Fin w) :
    (mod w).eval x i = (leftWord x % rightWord x).getLsbD i.val := by
  rw [mod, compileVec_correct]
  exact denote_blastUmod _ _ _ _ _ (binaryInputs_left w x) (binaryInputs_right w x) _ _

lemma mod_count (w : ℕ) : (mod w).net.count ≤ 216*w*w+56*w+6 := by
  have h := compileVec_count (blastUmod (inputs (w+w)).1 (binaryInputs w)).aig
    (blastUmod (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.mod_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [mod]
  nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
