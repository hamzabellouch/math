import Mathlib
import OAI.Computability.QuantumFactoring.NodeControlBounds
import OAI.Computability.QuantumFactoring.NodeStateCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.NodeStateCircuit
open BooleanNetwork

lemma pending_count (s w : ℕ) : (pending s w).net.count=0 := rfl
lemma output_count (s w : ℕ) : (output s w).net.count=0 := rfl
lemma bad_count (s w : ℕ) : (bad s w).net.count=0 := rfl
lemma old_count (s w : ℕ) : (old s w).net.count=0 := rfl
lemma supplied_count (s w : ℕ) : (supplied s w).net.count=0 := rfl
lemma nodeInput_count (s w : ℕ) : (nodeInput s w).net.count=0 := by
  simp only [nodeInput,count_pair,count_comp,old_count,pending_count,supplied_count,zero_add]
lemma top_count (s w : ℕ) : (top s w).net.count=0 := by
  simp only [top,count_comp,pending_count,blockNet_count,zero_add]
lemma nextPending_count (s w : ℕ) : (nextPending s w).net.count ≤ NodeCircuit.nextBound s w := by
  simpa only [nextPending,count_comp,nodeInput_count,zero_add] using NodeCircuit.next_count s w
lemma emission_count (s w : ℕ) : (emission s w).net.count ≤ NodeCircuit.primeBound w+8*w := by
  simpa only [emission,count_comp,nodeInput_count,zero_add] using NodeCircuit.emitted_count s w

def outputBound (s w : ℕ) :=
  NodeCircuit.primeBound w+8*w+97*w+21+(s+1)*w*(NodeCircuit.primeBound w+8*w)+7*((s+1)*w)
def stepBound (s w : ℕ) := NodeCircuit.nextBound s w+outputBound s w+
  (97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9)

lemma nextOutput_count (s w : ℕ) : (nextOutput s w).net.count ≤ outputBound s w := by
  have hz := zeroWord_count (emission s w)
  have he := emission_count s w
  have hs := stackPush_count (emission s w) ((old s w).comp (output s w))
  simp only [count_comp,old_count,output_count,add_zero] at hs
  have hs' : (stackPush (emission s w) ((old s w).comp (output s w))).net.count ≤
      (s+1)*w*(NodeCircuit.primeBound w+8*w) := hs.trans (Nat.mul_le_mul_left _ he)
  simp only [nextOutput,wordMux_count,count_comp,old_count,output_count,add_zero]
  dsimp only [outputBound]
  omega
lemma nextBad_count (s w : ℕ) : (nextBad s w).net.count ≤
    97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9 := by
  calc
    (nextBad s w).net.count = (NodeCircuit.failed s w).net.count+4 := by
      simp only [nextBad,count_bor,count_comp,old_count,bad_count,nodeInput_count,zero_add]
    _ ≤ (97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+5)+4 :=
      Nat.add_le_add_right (NodeCircuit.failed_count s w) 4
    _ = 97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9 := by omega

theorem step_count (s w : ℕ) : (step s w).net.count ≤ stepBound s w := by
  have h1 := nextPending_count s w
  have h2 := nextOutput_count s w
  have h3 := nextBad_count s w
  simp only [step,count_pair]
  exact Nat.add_le_add (Nat.add_le_add h1 h2) h3

end ExactQuantumFactoring.BitArithmetic.NodeStateCircuit


end

end OAI
