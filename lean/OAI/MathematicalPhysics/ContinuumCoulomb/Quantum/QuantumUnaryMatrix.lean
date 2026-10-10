import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryEmbeddingEnergy

namespace OAI

/-! The actual Hermitian matrix on all clock and computation qubits. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMAUnaryRow (c : QMACircuit) := Fin c.gates.length × QMAUnaryBasis c

def qmaUnaryPropagationMap (c : QMACircuit) :
    (QMAUnaryBasis c → ℂ) →ₗ[ℂ] (QMAUnaryRow c → ℂ) where
  toFun u p := if QMAClockGuard c.gates.length p.1 p.2.1 ∧
      p.2.1 (qmaClockMiddle c.gates.length p.1) = 0 then
    qmaUnaryResidual c u p.1 p.2.1 p.2.2 else 0
  map_add' u v := by
    funext p
    by_cases h : QMAClockGuard c.gates.length p.1 p.2.1 ∧
        p.2.1 (qmaClockMiddle c.gates.length p.1) = 0
    · simp only [ite_eq_left h,Pi.add_apply]
      change (u _+v _)-(qmaStepMatrix c p.1.val).mulVec
        ((fun a => u (p.2.1,a))+(fun a => v (p.2.1,a))) p.2.2 = _
      rw [Matrix.mulVec_add]
      simp only [qmaUnaryResidual,Pi.add_apply]
      ring
    · simp only [ite_eq_right h,Pi.add_apply,add_zero]
  map_smul' a u := by
    funext p
    by_cases h : QMAClockGuard c.gates.length p.1 p.2.1 ∧
        p.2.1 (qmaClockMiddle c.gates.length p.1) = 0
    · simp only [ite_eq_left h,Pi.smul_apply,RingHom.id_apply]
      change a*u _-(qmaStepMatrix c p.1.val).mulVec
        (a • (fun b => u (p.2.1,b))) p.2.2 = _
      rw [Matrix.mulVec_smul]
      simp only [qmaUnaryResidual,Pi.smul_apply,smul_eq_mul]
      ring
    · simp only [ite_eq_right h,Pi.smul_apply,RingHom.id_apply,smul_zero]

def qmaUnaryPropagationMatrix (c : QMACircuit) : Matrix (QMAUnaryRow c) (QMAUnaryBasis c) ℂ :=
  LinearMap.toMatrix' (qmaUnaryPropagationMap c)

def qmaUnaryClockDiagonal (c : QMACircuit) (p : QMAUnaryBasis c) : ℝ :=
  qmaPinnedClockPenalty c.gates.length p.1

def qmaUnaryInputDiagonal (c : QMACircuit) (p : QMAUnaryBasis c) : ℝ :=
  if p.1 (qmaInputMarker c) = 0 then qmaAncillaCount c p.2 else 0

def qmaUnaryOutputDiagonal (c : QMACircuit) (p : QMAUnaryBasis c) : ℝ :=
  if p.1 (qmaOutputMarker c) = 1 ∧ p.2 (Fin.last c.work) ≠ 1 then 1 else 0

def qmaUnaryHamiltonian (c : QMACircuit) : Matrix (QMAUnaryBasis c) (QMAUnaryBasis c) ℂ :=
  Matrix.diagonal (fun p => (qmaUnaryClockDiagonal c p : ℂ))+
    Matrix.diagonal (fun p => (qmaUnaryOutputDiagonal c p : ℂ))+
    (7:ℂ) • Matrix.diagonal (fun p => (qmaUnaryInputDiagonal c p : ℂ))+
    (8*c.gates.length:ℂ) • ((qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c)

theorem qmaUnaryPropagationMatrix_form (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic ((qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c) u =
      qmaUnaryPropagationEnergy c u := by
  rw [qmaQuadratic_gram,qmaUnaryPropagationMatrix,LinearMap.toMatrix'_mulVec]
  simp [Fintype.sum_prod_type,qmaUnaryPropagationMap,qmaUnaryPropagationEnergy,
    apply_ite,Finset.sum_ite_irrel]

theorem qmaUnaryHamiltonian_hermitian (c : QMACircuit) : (qmaUnaryHamiltonian c).IsHermitian := by
  have hd (d : QMAUnaryBasis c → ℝ) : (Matrix.diagonal (fun p => (d p : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro p
    simp [isSelfAdjoint_iff]
  exact (((hd _).add (hd _)).add ((hd _).smul (by simp))).add
    ((Matrix.isHermitian_conjTranspose_mul_self (qmaUnaryPropagationMatrix c)).smul
      (by simp [isSelfAdjoint_iff]))

theorem qmaUnaryHamiltonian_form (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic (qmaUnaryHamiltonian c) u = qmaUnaryEnergy c u := by
  unfold qmaUnaryHamiltonian
  rw [qmaQuadratic_add,qmaQuadratic_add,qmaQuadratic_add]
  have hs : (8*c.gates.length:ℂ) = ((8*(c.gates.length:ℝ):ℝ):ℂ) := by push_cast; rfl
  have h7 : (7:ℂ) = ((7:ℝ):ℂ) := by norm_num
  rw [hs,h7,qmaQuadratic_smul,qmaQuadratic_smul,qmaQuadratic_diagonal_real,
    qmaQuadratic_diagonal_real,qmaQuadratic_diagonal_real,qmaUnaryPropagationMatrix_form]
  simp only [qmaUnaryEnergy,qmaUnaryClockEnergy,qmaUnaryOutputEnergy,qmaUnaryInputEnergy,
    qmaUnaryClockDiagonal,qmaUnaryOutputDiagonal,qmaUnaryInputDiagonal,Fintype.sum_prod_type,
    ite_mul,one_mul,zero_mul,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.mul_sum]

end ContinuumCoulomb

end

end OAI
