import Mathlib

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Little-endian computational wires, with the same bit ordering as the
manuscript and input/output interface. -/
def bitsValue : {b : ℕ} → (Fin b → Bool) → BitVec b
  | 0, _ => 0
  | b+1, x => BitVec.cons (x (Fin.last b)) (bitsValue (fun i => x i.castSucc))

lemma bitsValue_bit {b : ℕ} (x : Fin b → Bool) (i : Fin b) :
    (bitsValue x).getLsbD i.val = x i := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [bitsValue, Fin.val_last, BitVec.getLsbD_cons, ite_true]
    · simp only [bitsValue, BitVec.getLsbD_cons, Fin.val_castSucc,
        ite_eq_right (Nat.ne_of_lt j.isLt)]
      exact ih _ j

lemma bitsValue_bits {b : ℕ} (x : BitVec b) :
    bitsValue (fun i : Fin b => x.getLsbD i.val) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact bitsValue_bit _ ⟨i,hi⟩

def bitsEquiv (b : ℕ) : (Fin b → Bool) ≃ BitVec b where
  toFun := bitsValue
  invFun := fun x i => x.getLsbD i.val
  left_inv := by intro x; funext i; exact bitsValue_bit x i
  right_inv := bitsValue_bits

/-- The exact integer in the two most significant wires is the quarter-bin. -/
lemma bitsValue_quarter (b : ℕ) (x : Fin (b+2) → Bool) :
    (bitsValue x).toNat / 2^b =
      2*(x (Fin.last (b+1))).toNat + (x ((Fin.last b).castSucc)).toNat := by
  have hlow := (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).isLt
  simp only [bitsValue, BitVec.toNat_cons', Nat.shiftLeft_eq]
  have he : (x (Fin.last (b+1))).toNat * 2^(b+1) +
      ((x ((Fin.last b).castSucc)).toNat * 2^b +
        (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).toNat) =
      (2*(x (Fin.last (b+1))).toNat + (x ((Fin.last b).castSucc)).toNat) * 2^b +
        (bitsValue (fun i : Fin b => x i.castSucc.castSucc)).toNat := by
    rw [pow_succ]
    ring
  rw [he, Nat.mul_comm _ (2^b), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hlow, Nat.add_zero]

end ExactQuantumFactoring


end

end OAI
