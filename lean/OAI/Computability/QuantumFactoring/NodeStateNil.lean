import Mathlib
import OAI.Computability.QuantumFactoring.NodeStateCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

lemma zeroBasis_value (w : ℕ) : bitsValue (fun _ : Fin w=>false)=(0 : BitVec w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bitsValue_bit _ ⟨i,hi⟩]
  simp

namespace NodeCircuit
lemma done_nil (s w : ℕ) (d : Basis w) : (isDone s w).eval (pack [] d) 0=true := by
  rw [isDone_pack]
  simp only [List.head?_nil,Option.getD_none,zeroBasis_value]
  rfl
lemma notPrime_nil {s w : ℕ} (hw : 128 ≤ w) (d : Basis w) :
    (isPrime s w).eval (pack [] d) 0≠true := by
  intro h
  rw [isPrime,eval_comp] at h
  have hp := (primeWord_value hw ((top s w).eval (pack [] d))).mp h
  rw [top_pack] at hp
  simp only [List.head?_nil,Option.getD_none,zeroBasis_value] at hp
  exact Nat.not_prime_zero hp
lemma next_nil (s w : ℕ) (d : Basis w) :
    (next s w).eval (pack [] d)=stackEncoding (s+1) w [] := by
  rw [next,wordMux_eval,ite_eq_left (done_nil s w d),pending_pack]
lemma emitted_nil {s w : ℕ} (hw : 128≤w) (d : Basis w) :
    (emitted s w).eval (pack [] d)=(fun _=>false) := by
  rw [emitted,wordMux_eval,ite_eq_right (notPrime_nil hw d)]
  funext i
  simp [wordConstant]
lemma failed_nil (s w : ℕ) (d : Basis w) :
    (failed s w).eval (pack [] d) 0=false := by
  rw [failed,eval_band,eval_band,eval_bnot,done_nil]
  rfl
end NodeCircuit

namespace NodeStateCircuit
lemma step_nil {s w : ℕ} (hw : 128 ≤ w) (d : Basis w) (ys : List (Basis w)) (b : Bool) :
    (step s w).eval (Fin.append (pack [] ys b) d)=pack [] ys b := by
  have he : (emission s w).eval (Fin.append (pack [] ys b) d)=(fun _=>false) := by
    rw [emission,eval_comp,nodeInput_pack,NodeCircuit.emitted_nil hw]
  have hz : (zeroWord (emission s w)).eval (Fin.append (pack [] ys b) d) 0=true := by
    rw [zeroWord_value,he,zeroBasis_value]
    rfl
  rw [step,eval_pair,eval_pair,nextPending,eval_comp,nodeInput_pack,
    NodeCircuit.next_nil,nextOutput,wordMux_eval,ite_eq_left hz,eval_comp,old_append,output_pack,
    nextBad_pack _ _ _ _ (NodeCircuit.failed_nil s w d)]
  rfl
end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
