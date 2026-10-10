import Mathlib
import OAI.Computability.QuantumFactoring.BitStackNaturals
import OAI.Computability.QuantumFactoring.BitStackFold

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma binaryValue_append (xs ys : List Bool) :
    binaryValue (xs++ys)=binaryValue xs+2^xs.length*binaryValue ys := by
  induction xs with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.cons_append,List.length_cons,binaryValue,ih,pow_succ]
    ring

lemma bigEndian_value (xs : List Bool) (a : ℕ) :
    xs.foldl (bitAction (fun n=>2*n) (fun n=>2*n+1)) a=
      binaryValue xs.reverse+2^xs.length*a := by
  induction xs generalizing a with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    simp only [List.foldl_cons,ih,List.reverse_cons,binaryValue_append,
      List.length_reverse,List.length_cons,pow_succ]
    cases b <;> simp [bitAction,binaryValue] <;> ring

lemma double_bits_length (n : ℕ) : (2*n).bits.length≤n.bits.length+1 := by
  by_cases h : n=0
  · subst n;simp
  · rw [Nat.bit0_bits n h,List.length_cons]
lemma doubleOne_bits_length (n : ℕ) : (2*n+1).bits.length≤n.bits.length+1 := by
  rw [Nat.bit1_bits,List.length_cons]

namespace Procedure
noncomputable def double : Procedure Nat.bits Nat.bits (fun n=>2*n) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip (.seq (.push () false) (.push () false))
    (.seq (.push () true) (.push () false))
  bound:=Polynomial.C 3
  runs n:=by
    by_cases hn : n=0
    · subst n
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    · have he : n.bits≠[]:=by
        intro h
        have hv:=binaryValue_bits n
        rw [h] at hv
        exact hn hv.symm
      cases hb : n.bits with
      | nil=>exact (he hb).elim
      | cons b bs=>
        have hout : (2*n).bits=false::b::bs:=by rw [Nat.bit0_bits n hn,hb]
        have hbody : Runs (.seq (.push () b) (.push () false))
            (singletonStore () bs) (singletonStore () (false::b::bs)) 2:=by
          have hh:=Runs.seq (Runs.push (singletonStore () bs) () b)
            (Runs.push (singletonStore () (b::bs)) () false)
          simpa only [singletonStore,Function.update_self,Function.update_idem] using hh
        refine ⟨3,by simp,?_⟩
        rw [hout]
        cases b
        · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)
        · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa [singletonStore] using hbody)

noncomputable def doubleOne : Procedure Nat.bits Nat.bits (fun n=>2*n+1) :=
  (prepend Nat.bits [true]).result (by intro n;simp only [List.singleton_append,Nat.bit1_bits,id_eq])

/-- Canonicalize a binary word, charging a linear-growth bit fold. -/
noncomputable def normalize : Procedure (id : List Bool→List Bool) Nat.bits binaryValue := by
  let p:=foldBitsLinear double doubleOne 1 double_bits_length doubleOne_bits_length
  let start:=reverse.pair (constant (id : List Bool→List Bool) Nat.bits 0)
  exact (p.comp start).congrFun (by intro xs;simp [bigEndian_value])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
