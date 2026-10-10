import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFiniteHistory
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace OAI

/-! The actual finite Hermitian circuit-history Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMAPropagationBasis (c : QMACircuit) :=
  Fin c.gates.length × SourceSpinBasis (c.work+1)

def qmaPropagationMap (c : QMACircuit) :
    (QMAHistoryBasis c → ℂ) →ₗ[ℂ] (QMAPropagationBasis c → ℂ) where
  toFun u ts :=
    u (⟨ts.1.val+1,Nat.succ_lt_succ ts.1.isLt⟩,ts.2)-
    (qmaStepMatrix c ts.1.val).mulVec
      (fun s => u (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s)) ts.2
  map_add' u v := by
    funext ts
    change (u _+v _)-(qmaStepMatrix c ts.1.val).mulVec
      ((fun s => u (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s))+
       (fun s => v (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s))) ts.2 = _
    rw [Matrix.mulVec_add]
    simp only [Pi.add_apply]
    ring
  map_smul' a u := by
    funext ts
    change a*u _-(qmaStepMatrix c ts.1.val).mulVec
      (a • (fun s => u (⟨ts.1.val,ts.1.isLt.trans (Nat.lt_succ_self _)⟩,s))) ts.2 = _
    rw [Matrix.mulVec_smul]
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

def qmaPropagationMatrix (c : QMACircuit) :
    Matrix (QMAPropagationBasis c) (QMAHistoryBasis c) ℂ :=
  LinearMap.toMatrix' (qmaPropagationMap c)

def qmaInitialDiagonal (c : QMACircuit) (p : QMAHistoryBasis c) : ℂ :=
  if p.1.val = 0 ∧ ¬QMAAncillaZero c p.2 then 1 else 0

def qmaFinalDiagonal (c : QMACircuit) (p : QMAHistoryBasis c) : ℂ :=
  if p.1.val = c.gates.length ∧ p.2 (Fin.last c.work) ≠ 1 then 1 else 0

def qmaHistoryHamiltonian (c : QMACircuit) : Matrix (QMAHistoryBasis c) (QMAHistoryBasis c) ℂ :=
  Matrix.diagonal (qmaFinalDiagonal c)+
    (7:ℂ) • Matrix.diagonal (qmaInitialDiagonal c)+
    (8*c.gates.length:ℂ) • ((qmaPropagationMatrix c).conjTranspose*qmaPropagationMatrix c)

theorem qmaHistoryHamiltonian_hermitian (c : QMACircuit) :
    (qmaHistoryHamiltonian c).IsHermitian := by
  have hi : (Matrix.diagonal (qmaInitialDiagonal c)).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro p
    unfold qmaInitialDiagonal
    split <;> simp
  have ho : (Matrix.diagonal (qmaFinalDiagonal c)).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro p
    unfold qmaFinalDiagonal
    split <;> simp
  exact (ho.add (hi.smul (by simp))).add
    ((Matrix.isHermitian_conjTranspose_mul_self (qmaPropagationMatrix c)).smul (by simp [isSelfAdjoint_iff]))

end ContinuumCoulomb

end

end OAI
