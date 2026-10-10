import Mathlib
import OAI.Computability.QuantumFactoring.WordNetworks

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Ordinary zero extension/truncation, without copying a word circuit once per bit. -/
def resizeWord (u w : ℕ) : BooleanNetwork u w :=
  vector (fun i => if h : i.val<u then bit ⟨i.val,h⟩ else constant false)

lemma resizeWord_value (u w : ℕ) (x : Basis u) :
    bitsValue ((resizeWord u w).eval x)=(bitsValue x).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((resizeWord u w).eval x)).getLsbD i =
    (resizeWord u w).eval x ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_setWidth]
  simp only [hi,decide_true,Bool.true_and,resizeWord,eval_vector]
  by_cases hu : i<u
  · rw [dite_eq_left hu,eval_bit]
    exact (bitsValue_bit x ⟨i,hu⟩).symm
  · rw [dite_eq_right hu]
    simpa only [eval_constant] using (BitVec.getLsbD_of_ge (bitsValue x) i (by omega)).symm

lemma resizeWord_count (u w : ℕ) : (resizeWord u w).net.count≤w := by
  have hh := count_vector_le (c:=1)
    (fun i : Fin w => if h : i.val<u then bit ⟨i.val,h⟩ else constant false) (by
      intro i
      by_cases h : i.val<u
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=bit ⟨i.val,h⟩ := dite_eq_left h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp)
      · have he : (if h : i.val<u then bit (n:=u) ⟨i.val,h⟩ else constant false)=constant false := dite_eq_right h
        exact (congrArg (fun c : BooleanNetwork u 1 => c.net.count) he).trans_le (by simp))
  simpa only [resizeWord,mul_one] using hh

lemma resizeWord_toNat {u w : ℕ} (h : u≤w) (x : Basis u) :
    (bitsValue ((resizeWord u w).eval x)).toNat=(bitsValue x).toNat := by
  rw [resizeWord_value,setWidth_toNat_of_le h]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
