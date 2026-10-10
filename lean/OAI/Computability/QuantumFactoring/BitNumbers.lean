import Mathlib
import OAI.Computability.QuantumFactoring.BitEncoding

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma bitsValue_toNat {b : ℕ} (x : Fin b → Bool) :
    (bitsValue x).toNat = ∑ i : Fin b, 2^i.val*(x i).toNat := by
  induction b with
  | zero => simp [bitsValue]
  | succ b ih =>
    rw [bitsValue, BitVec.toNat_cons', Nat.shiftLeft_eq, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Fin.val_castSucc]
    ring

lemma bitsValue_ofFn {b : ℕ} (v : Fin (2^b)) :
    (bitsValue (fun i : Fin b => v.val.testBit i.val)).toNat = v.val := by
  have he : (fun i : Fin b => v.val.testBit i.val) =
      (fun i : Fin b => (BitVec.ofNat b v.val).getLsbD i.val) := by simp
  rw [he, bitsValue_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt v.isLt]

end ExactQuantumFactoring


end

end OAI
