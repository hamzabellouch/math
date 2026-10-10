import Mathlib.Logic.Equiv.Fin.Basic
import OAI.NumberTheory.Ostmann.Characters.OneSidedCharacterBound

namespace OAI

/-! # Exact residue-progressions in a padded integer interval -/

namespace Ostmann

/-- Row/column transposition lists each residue class in increasing order. -/
def integerProgressionPartition (Q K : ℕ) : Fin (K * Q) ≃ Σ _ : Fin Q, Fin K :=
  finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin K) (Fin Q)).trans
    (Equiv.sigmaEquivProd (Fin Q) (Fin K)).symm)

theorem integerProgressionPartition_value (Q K a : ℕ) (r : Fin Q) (j : Fin K) :
    a + ((integerProgressionPartition Q K).symm ⟨r, j⟩).val = (a + r.val) + Q * j.val := by
  change a + (r.val + Q * j.val) = _
  omega

/-- An interval can be padded by at most one modulus to get this exact
rectangular decomposition; original support indicators can retain its endpoints. -/
theorem integerProgressionPartition_padding (N Q : ℕ) (hQ : 0 < Q) :
    N < (N / Q + 1) * Q ∧ (N / Q + 1) * Q ≤ N + Q := by
  have hmod := Nat.mod_lt N hQ
  have he : N / Q * Q + N % Q = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N Q
  rw [Nat.add_mul, one_mul]
  omega

/-- Reindexing the original integer sum introduces neither missing boundary
integers nor multiplicity. -/
theorem integerProgressionPartition_sum {M : Type*} [AddCommMonoid M]
    (Q K : ℕ) (f : Fin (K * Q) → M) :
    (∑ x, f x) = ∑ r : Fin Q, ∑ j : Fin K,
      f ((integerProgressionPartition Q K).symm ⟨r, j⟩) := by
  rw [← (integerProgressionPartition Q K).symm.sum_comp f, Fintype.sum_sigma]

end Ostmann

end OAI
