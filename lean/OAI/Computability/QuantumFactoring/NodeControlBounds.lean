import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifierBounds
import OAI.Computability.QuantumFactoring.NodeControlCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma properOn_count {k w : ℕ} (m d : BooleanNetwork k w) :
    (properOn m d).net.count ≤ 2*m.net.count+3*d.net.count+216*w*w+250*w+45 := by
  have h1 := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 1)) d
  have h2 := wordLt_count d m
  have h3 := zeroWord_count ((m.pair d).comp (mod w))
  have h4 := mod_count w
  simp only [wordConstant_count] at h1
  simp only [count_comp,count_pair] at h3
  simp only [properOn,count_band]
  omega

namespace NodeCircuit

def primeBound (w : ℕ) := 49*w+10+rootWidth w+primalityBound w
def guardBound (w : ℕ) := 216*w*w+250*w+45
def quotientBound (w : ℕ) := 216*w*w+56*w+6
def splitBound (s w : ℕ) := ((s+1)*w)*(((s+1)*w)*(quotientBound w+(s+1)*w*w))
def nextBound (s w : ℕ) := 97*w+21+primeBound w+(s+1)*w*w+guardBound w+
  splitBound s w+21*((s+1)*w)
def stepBound (s w : ℕ) := nextBound s w+2*primeBound w+guardBound w+105*w+26

@[simp] lemma pending_count (s w : ℕ) : (pending s w).net.count=0 := rfl
@[simp] lemma top_count (s w : ℕ) : (top s w).net.count=0 := rfl
@[simp] lemma divisor_count (s w : ℕ) : (divisor s w).net.count=0 := rfl
lemma popped_count (s w : ℕ) : (popped s w).net.count ≤ (s+1)*w*w := by
  simpa only [popped,count_comp,pending_count,zero_add] using stackPop_count (s+1) w
lemma quotient_count (s w : ℕ) : (quotient s w).net.count ≤ quotientBound w := by
  simpa only [quotient,quotientBound,count_comp,count_pair,top_count,divisor_count,zero_add]
    using div_count w
lemma isPrime_count (s w : ℕ) : (isPrime s w).net.count ≤ primeBound w := by
  simpa only [isPrime,primeBound,count_comp,top_count,zero_add] using primeWord_count w
lemma isDone_count (s w : ℕ) : (isDone s w).net.count ≤ 97*w+21 := by
  simpa only [isDone,top_count,zero_add] using zeroWord_count (top s w)
lemma isProper_count (s w : ℕ) : (isProper s w).net.count ≤ guardBound w := by
  simpa only [isProper,guardBound,top_count,divisor_count,mul_zero,zero_add] using
    properOn_count (top s w) (divisor s w)
lemma split_count (s w : ℕ) : (split s w).net.count ≤ splitBound s w := by
  have h1 := stackPush_count (quotient s w) (popped s w)
  have h2 := stackPush_count (divisor s w) (stackPush (quotient s w) (popped s w))
  rw [divisor_count,zero_add] at h2
  exact h2.trans (Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _
    (Nat.add_le_add (quotient_count s w) (popped_count s w)))))
lemma next_count (s w : ℕ) : (next s w).net.count ≤ nextBound s w := by
  have h1 := isDone_count s w
  have h2 := isPrime_count s w
  have h3 := isProper_count s w
  have h4 := popped_count s w
  have h5 := split_count s w
  simp only [next,wordMux_count,pending_count]
  dsimp only [nextBound]
  omega
lemma emitted_count (s w : ℕ) : (emitted s w).net.count ≤ primeBound w+8*w := by
  have h := isPrime_count s w
  simp only [emitted,wordMux_count,top_count,wordConstant_count]
  omega
lemma failed_count (s w : ℕ) : (failed s w).net.count ≤ 97*w+21+primeBound w+guardBound w+5 := by
  have h1 := isDone_count s w
  have h2 := isPrime_count s w
  have h3 := isProper_count s w
  simp only [failed,count_band,count_bnot]
  omega

/-- Explicit polynomial-size bound for the full guarded one-step controller. -/
theorem step_count (s w : ℕ) : (step s w).net.count ≤ stepBound s w := by
  have h1 := next_count s w
  have h2 := emitted_count s w
  have h3 := failed_count s w
  simp only [step,count_pair]
  dsimp only [stepBound]
  omega

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
