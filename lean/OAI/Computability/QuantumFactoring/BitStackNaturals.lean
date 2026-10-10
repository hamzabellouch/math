import Mathlib
import OAI.Computability.QuantumFactoring.BitStackBasicProcedures
import OAI.Computability.QuantumFactoring.BitStackConstants
import OAI.Computability.QuantumFactoring.BitStackIncrement
import OAI.Computability.QuantumFactoring.BitStackIteration

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_bits (n : ℕ) : binaryValue n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [binaryValue,ih,Nat.bit,Nat.add_comm]

lemma incrementWord_bits (n : ℕ) : incrementWord n.bits=(n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b
    · simp only [incrementWord,Nat.bit_false,Nat.bit1_bits]
    · simp only [incrementWord,ih,Nat.bit_true]
      rw [show 2*n+1+1=2*(n+1) by omega,Nat.bit0_bits (n+1) (by omega)]

abbrev unaryCode (n : ℕ) := List.replicate n true
namespace Procedure
noncomputable def successor : Procedure Nat.bits Nat.bits Nat.succ where
  K:=Fin 3
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=increment 0 1 2
  bound:=Polynomial.C 6*Polynomial.X+Polynomial.C 6
  runs n:=by
    have hh:=increment_runs (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
      (singletonStore 0 n.bits) (by simp [singletonStore]) (by simp [singletonStore])
    refine ⟨6*carryCount n.bits+6,?_,?_⟩
    · have hl:=carryCount_le_length n.bits
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
      omega
    · simpa [singletonStore,incrementWord_bits] using hh

noncomputable def unarySuccessor : Procedure unaryCode unaryCode Nat.succ where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.push () true
  bound:=1
  runs n:=by
    refine ⟨1,by simp,?_⟩
    simpa [singletonStore,unaryCode,List.replicate_succ] using
      Runs.push (singletonStore () (unaryCode n)) () true

/-- Unary-to-binary conversion charges every carry and all word moves. -/
noncomputable def unaryToBits : Procedure unaryCode Nat.bits id := by
  let p:=successor.iterate (Polynomial.X+1) (by
    intro n a i hi
    have hlen : (a+i).bits.length≤a.bits.length+i := by
      clear hi
      induction i with
      | zero => simp
      | succ i ih =>
        have h:=incrementWord_length (a+i).bits
        rw [incrementWord_bits] at h
        simpa only [Nat.add_assoc] using (h.trans (Nat.add_le_add_right ih 1))
    simpa only [Function.iterate_succ_apply',Function.iterate_succ_apply,
      Nat.succ_iterate,Nat.size_eq_bits_len,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one] using (hlen.trans (by omega : a.bits.length+i≤n+a.bits.length+1)))
  exact (p.comp ((identity unaryCode).pair (constant unaryCode Nat.bits 0))).congrFun
    (by intro n; simp [Nat.succ_iterate])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
