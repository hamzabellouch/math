import Mathlib
import OAI.Computability.QuantumFactoring.FactoringInputLayout

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
/-- Move the physical input after the branch bit to the front, and place the
readout immediately after the true input. The retained history is permuted,
never erased or initialized with input-dependent advice. -/
def relocateVal (A m ℓ i : ℕ) : ℕ :=
  if i=0 then ℓ+m else if i≤ℓ then i-1 else if i<A then i+m
  else if i<A+m then ℓ+(i-A) else i

lemma relocateVal_lt {A m ℓ r i : ℕ} (hl : ℓ+1≤A) (hi : i<A+m+r) :
    relocateVal A m ℓ i<A+m+r := by
  unfold relocateVal
  split_ifs <;> omega

lemma relocateVal_injective {A m ℓ r : ℕ} (hl : ℓ+1≤A) :
    Function.Injective (fun i : Fin (A+m+r) => relocateVal A m ℓ i.val) := by
  intro i j h
  apply Fin.ext
  have hi:=i.isLt
  have hj:=j.isLt
  dsimp only at h
  unfold relocateVal at h
  split_ifs at h <;> omega

def relocate (A m ℓ r : ℕ) (hl : ℓ+1≤A) : Register (A+m+r) (A+m+r) where
  toFun i:=⟨relocateVal A m ℓ i.val,relocateVal_lt hl i.isLt⟩
  inj' := by
    intro i j h
    exact relocateVal_injective hl (congrArg Fin.val h)

lemma relocate_input (A m ℓ r N : ℕ) (hl : ℓ+1≤A) :
    inputBasis (A+m+r) ℓ N ∘ relocate A m ℓ r hl = shiftedInput (A+m+r) ℓ N := by
  funext i
  change (if relocateVal A m ℓ i.val < ℓ then N.testBit (relocateVal A m ℓ i.val) else false)=_
  unfold shiftedInput relocateVal
  split_ifs <;> simp_all <;> omega

lemma relocate_output (A m ℓ r : ℕ) (hl : ℓ+1≤A) (j : Fin m) :
    (relocate A m ℓ r hl) ⟨A+j.val,by omega⟩=⟨ℓ+j.val,by have:=j.isLt;omega⟩ := by
  apply Fin.ext
  change relocateVal A m ℓ (A+j.val)=ℓ+j.val
  have hj:=j.isLt
  unfold relocateVal
  split_ifs <;> omega

lemma shiftedInput_pad (q n ℓ N : ℕ) (hl : ℓ≤n) (hb : N<2^ℓ) :
    shiftedInput q ℓ N=shiftedInput q n N := by
  funext i
  unfold shiftedInput
  by_cases hi : 1 ≤ i.val ∧ i.val < 1+ℓ
  · rw [ite_eq_left hi,ite_eq_left (by omega)]
  · rw [ite_eq_right hi]
    split_ifs with hj
    · have hb' : N<2^(i.val-1) := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))
      rw [Nat.testBit_lt_two_pow hb']
    · rfl
end ExactQuantumFactoring


end

end OAI
