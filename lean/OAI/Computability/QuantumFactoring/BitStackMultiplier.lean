import Mathlib
import OAI.Computability.QuantumFactoring.BitStackSubtractor

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma bits_length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

lemma bits_length_value (xs : List Bool) : (binaryValue xs).bits.length≤xs.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact binaryValue_lt xs

lemma bits_length_add (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hap : 2^a.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  have hbp : 2^b.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  rw [pow_succ]
  omega

lemma bits_length_mul (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le,pow_add]
  have h:=Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
  simpa only [Nat.size_eq_bits_len] using h

lemma bits_length_pow2 (n : ℕ) : (2^n).bits.length=n+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_pow]

def mulZeroStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2)
def mulOneStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2+x.1)

lemma mul_fold (xs : List Bool) (x : ℕ×ℕ) :
    xs.foldl (bitAction mulZeroStep mulOneStep) x=
      (x.1,x.1*binaryValue xs.reverse+2^xs.length*x.2) := by
  induction xs generalizing x with
  | nil=>simp [binaryValue]
  | cons b bs ih=>
    rw [List.foldl_cons,ih]
    simp only [List.reverse_cons,binaryValue_append,List.length_reverse,List.length_cons,
      binaryValue,pow_succ]
    cases b <;> simp [bitAction,mulZeroStep,mulOneStep] <;> ring

namespace Procedure
noncomputable def mulZeroStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulZeroStep :=
  ((first Nat.bits Nat.bits).pair (double.comp (second Nat.bits Nat.bits))).congrFun (by intro x;rfl)
noncomputable def mulOneStepP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) mulOneStep := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  exact (first.pair (binaryAdd.comp ((double.comp second).pair first))).congrFun (by intro x;rfl)

noncomputable def mulFoldP : Procedure (prodCode id (prodCode Nat.bits Nat.bits))
    (prodCode Nat.bits Nat.bits) (fun x=>x.1.foldl (bitAction mulZeroStep mulOneStep) x.2) :=
  foldBits mulZeroStepP mulOneStepP (Polynomial.C 3*Polynomial.X+Polynomial.C 3) (by
    intro xs x i
    rw [mul_fold]
    simp only [prodCode,pairBits_length]
    have hs:=bits_length_add (x.1*binaryValue (xs.take i).reverse) (2^(xs.take i).length*x.2)
    have hm:=bits_length_mul x.1 (binaryValue (xs.take i).reverse)
    have hn:=bits_length_mul (2^(xs.take i).length) x.2
    have hv:=bits_length_value (xs.take i).reverse
    rw [List.length_reverse] at hv
    rw [bits_length_pow2] at hn
    have hl : (xs.take i).length≤xs.length:=by simp only [List.length_take];omega
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega)

noncomputable def binaryMul : Procedure (prodCode Nat.bits Nat.bits) Nat.bits
    (fun x=>x.1*x.2) := by
  let first:=first Nat.bits Nat.bits
  let second:=second Nat.bits Nat.bits
  let bits : Procedure Nat.bits (id : List Bool→List Bool) Nat.bits:=
    (identity (id : List Bool→List Bool)).precompose Nat.bits
  let start:=(reverse.comp (bits.comp second)).pair
    (first.pair (constant (prodCode Nat.bits Nat.bits) Nat.bits 0))
  exact ((Procedure.second Nat.bits Nat.bits).comp (mulFoldP.comp start)).congrFun (by
    intro x
    simp [mul_fold,binaryValue_bits])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
