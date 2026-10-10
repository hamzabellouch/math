import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRowTransfer

namespace OAI

/-! Intertwining identities for moving operators together with their active wires. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaWirePermutation_mul_matrix {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (s t : SourceSpinBasis n) :
    (qmaWirePermutation e*M) s t = M (e.symm s) t := by
  simp only [Matrix.mul_apply,qmaWirePermutation]
  rw [Finset.sum_eq_single (e.symm s)]
  · simp
  · intro b _ hb
    have h : s ≠ e b := fun he => hb ((e.eq_symm_apply.mpr he.symm))
    simp [h]
  · simp

theorem qmaMatrix_mul_wirePermutation {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (s t : SourceSpinBasis n) :
    (M*qmaWirePermutation e) s t = M s (e t) := by
  simp only [Matrix.mul_apply,qmaWirePermutation]
  rw [Finset.sum_eq_single (e t)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem qmaWirePermutation_intertwines {n : ℕ}
    (e : SourceSpinBasis n ≃ SourceSpinBasis n)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    qmaWirePermutation e*M = M.submatrix e.symm e.symm*qmaWirePermutation e := by
  ext s t
  rw [qmaWirePermutation_mul_matrix,qmaMatrix_mul_wirePermutation]
  simp

theorem qmaWireBasis_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (qmaWireBasis σ).symm = qmaWireBasis σ.symm := by
  ext s k
  rfl

theorem qmaGate_wire_intertwines (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) :
    qmaWirePermutation (qmaWireBasis σ)*qmaGateMatrix work g =
      qmaGateMatrix work (qmaRelabelGate work σ.symm g)*qmaWirePermutation (qmaWireBasis σ) := by
  rw [qmaWirePermutation_intertwines,qmaRelabelGate_matrix,qmaWireBasis_symm]
  rfl

theorem qmaGateProduct_wire_intertwines (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (gs : List QMAGate) :
    qmaWirePermutation (qmaWireBasis σ)*qmaGateProduct work gs =
      qmaGateProduct work (gs.map (qmaRelabelGate work σ.symm))*
        qmaWirePermutation (qmaWireBasis σ) := by
  rw [qmaGateProduct_relabel,qmaWirePermutation_intertwines,qmaWireBasis_symm]
  rfl

end ContinuumCoulomb

end

end OAI
