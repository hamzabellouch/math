import Mathlib
import OAI.Computability.QuantumFactoring.BitArithmeticDivision

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
namespace BitArithmetic
open BooleanNetwork

lemma leftWord_append {w : ℕ} (a b : Basis w) : leftWord (Fin.append a b) = bitsValue a := by
  simp [leftWord]
lemma rightWord_append {w : ℕ} (a b : Basis w) : rightWord (Fin.append a b) = bitsValue b := by
  simp only [rightWord, Fin.append_right]

lemma mul_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mul w).eval (Fin.append a b)) = bitsValue a * bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mul w).eval (Fin.append a b))).getLsbD i =
    (mul w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mul_correct, leftWord_append, rightWord_append]

lemma mod_word (w : ℕ) (a b : Basis w) :
    bitsValue ((mod w).eval (Fin.append a b)) = bitsValue a % bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((mod w).eval (Fin.append a b))).getLsbD i =
    (mod w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    mod_correct, leftWord_append, rightWord_append]

lemma add_word (w : ℕ) (a b : Basis w) :
    bitsValue ((add w).eval (Fin.append a b)) = bitsValue a + bitsValue b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue ((add w).eval (Fin.append a b))).getLsbD i =
    (add w).eval (Fin.append a b) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    add_correct, leftWord_append, rightWord_append]

lemma bitsValue_append_zero {w t : ℕ} (x : Basis w) :
    bitsValue (Fin.append x (fun _ : Fin t => false)) = (bitsValue x).setWidth (w+t) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (Fin.append x (fun _ : Fin t => false))).getLsbD i =
    Fin.append x (fun _ => false) ⟨i,hi⟩ from bitsValue_bit _ ⟨i,hi⟩,
    BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hw : i < w
  · have he : (⟨i,hi⟩ : Fin (w+t)) = (⟨i,hw⟩ : Fin w).castAdd t := Fin.ext rfl
    rw [he, Fin.append_left]
    exact (bitsValue_bit x ⟨i,hw⟩).symm
  · have he : (⟨i,hi⟩ : Fin (w+t)) = Fin.natAdd w (⟨i-w,by omega⟩ : Fin t) := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [he, Fin.append_right, BitVec.getLsbD_of_ge _ _ (by omega)]

lemma padRight_word (w t : ℕ) (x : Basis w) :
    bitsValue ((padRight w t).eval x) = (bitsValue x).setWidth (w+t) := by
  rw [eval_padRight, bitsValue_append_zero]

lemma bitsValue_take {w t : ℕ} (x : Basis (w+t)) :
    bitsValue (x ∘ (Fin.castAdd t)) = (bitsValue x).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (bitsValue (x ∘ Fin.castAdd t)).getLsbD i = x ((⟨i,hi⟩ : Fin w).castAdd t) from
    bitsValue_bit _ ⟨i,hi⟩, BitVec.getLsbD_setWidth]
  simp only [hi, decide_true, Bool.true_and]
  exact (bitsValue_bit x ((⟨i,hi⟩ : Fin w).castAdd t)).symm

lemma setWidth_toNat_of_le {w t : ℕ} (h : w ≤ t) (x : BitVec w) :
    (x.setWidth t).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)

/-- A word of constants uses at most one Boolean node per output bit. -/
def wordConstant {n : ℕ} {w : ℕ} (v : BitVec w) : BooleanNetwork n w :=
  vector (fun i => constant (v.getLsbD i.val))

lemma wordConstant_eval {n w : ℕ} (v : BitVec w) (x : Basis n) :
    bitsValue ((wordConstant v).eval x) = v := by
  have he : (wordConstant (n := n) v).eval x = fun i => v.getLsbD i.val := by
    funext i
    simp [wordConstant]
  rw [he, bitsValue_bits]

lemma wordConstant_count {n w : ℕ} (v : BitVec w) :
    (wordConstant (n := n) v).net.count = w := by
  simp [wordConstant]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
