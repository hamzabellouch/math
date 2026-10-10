import Mathlib
import OAI.Computability.QuantumFactoring.PhasePreparationConnection

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The fixed little-endian physical representation of a modular residue. -/
def basisResidue (b : ℕ) : Basis b ≃ ZMod (2^b) :=
  (basisNumber b).trans (ZMod.finEquiv (2^b)).toEquiv

lemma finEquiv_val {n : ℕ} [NeZero n] (z : Fin n) :
    (ZMod.finEquiv n z).val = z.val := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n => rfl

lemma basisResidue_val (b : ℕ) (x : Basis b) :
    (basisResidue b x).val = (bitsValue x).toNat := by
  exact finEquiv_val _

lemma basisResidue_eq (b : ℕ) (x : Basis b) :
    basisResidue b x = ((bitsValue x).toNat : ZMod (2^b)) := by
  rw [← basisResidue_val, ZMod.natCast_zmod_val]

lemma bitsValue_residue (b : ℕ) (z : ZMod (2^b)) :
    (bitsValue ((basisResidue b).symm z)).toNat = z.val := by
  rw [← basisResidue_val, Equiv.apply_symm_apply]

lemma basisResidue_bits (b : ℕ) (v : BitVec b) :
    basisResidue b (fun i => v.getLsbD i.val) = (v.toNat : ZMod (2^b)) := by
  rw [basisResidue_eq, bitsValue_bits]

lemma bitsValue_residue_add (b : ℕ) (z : ZMod (2^b)) (d : Basis b) :
    (fun i : Fin b => (bitsValue ((basisResidue b).symm z)+bitsValue d).getLsbD i.val) =
      (basisResidue b).symm (z+basisResidue b d) := by
  apply (basisResidue b).injective
  rw [basisResidue_bits, Equiv.apply_symm_apply, BitVec.toNat_add]
  rw [ZMod.natCast_mod, Nat.cast_add, bitsValue_residue, ZMod.natCast_zmod_val,
    basisResidue_eq]

lemma basisResidue_zero (b : ℕ) : basisResidue b (fun _ => false) = 0 := by
  rw [basisResidue_eq]
  have h : bitsValue (fun _ : Fin b => false) = (0 : BitVec b) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (fun _ : Fin b => false)).getLsbD i = false from bitsValue_bit _ ⟨i,hi⟩]
    simp
  rw [h]
  simp

end ExactQuantumFactoring


end

end OAI
