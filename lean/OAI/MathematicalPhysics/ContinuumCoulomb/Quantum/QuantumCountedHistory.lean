import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalInput

namespace OAI

/-! The actual history Hamiltonian with individual input-qubit penalties. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

def qmaCountedHistoryHamiltonian (c : QMACircuit) :
    Matrix (QMAHistoryBasis c) (QMAHistoryBasis c) ℂ :=
  Matrix.diagonal (qmaFinalDiagonal c)+
    (7:ℂ) • Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ))+
    (8*c.gates.length:ℂ) • ((qmaPropagationMatrix c).conjTranspose*qmaPropagationMatrix c)

theorem qmaCountedHistoryHamiltonian_hermitian (c : QMACircuit) :
    (qmaCountedHistoryHamiltonian c).IsHermitian := by
  have hi : (Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro k
    simp [isSelfAdjoint_iff]
  have ho : (Matrix.diagonal (qmaFinalDiagonal c)).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro p
    unfold qmaFinalDiagonal
    split <;> simp
  exact (ho.add (hi.smul (by simp))).add
    ((Matrix.isHermitian_conjTranspose_mul_self (qmaPropagationMatrix c)).smul
      (by simp [isSelfAdjoint_iff]))

theorem qmaCountedHistoryHamiltonian_form (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (qmaCountedHistoryHamiltonian c) u =
      qmaOutputPenalty c (qmaHistoryFromVector c u)+
      7*qmaQuadratic (Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ))) u+
      8*c.gates.length*qmaPropagationEnergy c (qmaHistoryFromVector c u) := by
  unfold qmaCountedHistoryHamiltonian
  rw [qmaQuadratic_add,qmaQuadratic_add]
  have hs : (8*c.gates.length:ℂ) = ((8*(c.gates.length:ℝ):ℝ):ℂ) := by push_cast; rfl
  have h7 : (7:ℂ) = ((7:ℝ):ℂ) := by norm_num
  rw [hs,h7,qmaQuadratic_smul,qmaQuadratic_smul,
    qmaFinalDiagonal_energy,qmaPropagationMatrix_energy]

theorem qmaCountedHistoryHamiltonian_dominates (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (qmaHistoryHamiltonian c) u ≤
      qmaQuadratic (qmaCountedHistoryHamiltonian c) u := by
  rw [qmaHistoryHamiltonian_form,qmaCountedHistoryHamiltonian_form]
  have h := qmaInitialCountDiagonal_energy_ge c u
  rw [qmaInitialDiagonal_energy] at h
  unfold qmaHistoryEnergy
  linarith

theorem qmaCountedHistoryHamiltonian_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (QMAHistoryBasis c)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaCountedHistoryHamiltonian c) (fun p => u p) := by
  exact (qmaHistoryHamiltonian_sound c hc hsound u).trans
    (mul_le_mul_of_nonneg_left (qmaCountedHistoryHamiltonian_dominates c (fun p => u p))
      (by positivity))

theorem qmaCountedHistoryHamiltonian_ideal (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaQuadratic (qmaCountedHistoryHamiltonian c)
      (fun k => qmaHistoryVector c (qmaIdealHistory c hc psi) k) =
      ‖qmaRejectVector c hc psi‖^2 := by
  rw [qmaCountedHistoryHamiltonian_form,qmaInitialCountDiagonal_ideal_zero,
    qmaHistoryVector_propagation,qmaIdealHistory_propagation]
  unfold qmaOutputPenalty
  rw [qmaHistoryVector_slice c _ c.gates.length le_rfl]
  simp only [qmaIdealHistory,qmaPrefixMatrix_length,qmaRejectVector,qmaOutputVector,
    mul_zero,add_zero]

theorem qmaCountedHistoryHamiltonian_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (QMAHistoryBasis c), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaCountedHistoryHamiltonian c) (fun p => u p) ≤ 1 := by
  let w := qmaHistoryVector c (qmaIdealHistory c hc psi)
  have hw : ‖w‖^2 = (c.gates.length+1:ℝ) := by
    simp only [w,qmaHistoryVector_norm,qmaIdealHistory_mass,hpsi,one_pow,mul_one]
  have hn : ‖w‖ ≠ 0 := by
    intro h
    rw [h] at hw
    have hp : (0:ℝ) < c.gates.length+1 := by positivity
    norm_num at hw
    linarith
  have he : 3*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaCountedHistoryHamiltonian c) (fun p => w p) ≤ ‖w‖^2 := by
    rw [hw]
    dsimp only [w]
    rw [qmaCountedHistoryHamiltonian_ideal]
    have h := mul_le_mul_of_nonneg_left (qmaRejectVector_of_accept c hc psi hpsi hacc)
      (by positivity : 0 ≤ 3*(c.gates.length+1:ℝ))
    nlinarith
  let v := ((‖w‖⁻¹:ℝ):ℂ) • w
  refine ⟨v,by simp [v,norm_smul,hn],?_⟩
  have hq : qmaQuadratic (qmaCountedHistoryHamiltonian c) (fun p => v p) =
      (‖w‖⁻¹)^2*qmaQuadratic (qmaCountedHistoryHamiltonian c) (fun p => w p) := by
    convert qmaQuadratic_vector_smul (qmaCountedHistoryHamiltonian c) (‖w‖⁻¹)
      (fun p => w p) using 1
    congr 1
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg (‖w‖⁻¹))
  have hi : (‖w‖⁻¹)^2*‖w‖^2 = 1 := by field_simp
  rw [hq]
  nlinarith

end ContinuumCoulomb

end

end OAI
