import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMask

namespace OAI

/-! The verifier acceptance probability is the exact endpoint projection
energy of its normalized zero-ancilla evolution. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def qmaInputVector (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  WithLp.toLp 2 (qmaInitialState c hc psi)

def qmaOutputVector (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaApplyMatrix (qmaCircuitMatrix c) (qmaInputVector c hc psi)

def qmaRejectVector (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaMask (fun s => s (Fin.last c.work) ≠ 1) (qmaOutputVector c hc psi)

theorem qmaInputVector_norm (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    ‖qmaInputVector c hc psi‖ = ‖psi‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simpa only [qmaInputVector,PiLp.toLp_apply,Complex.sq_norm,sourceSpinMass] using
    qmaInitialState_mass c hc psi

theorem qmaOutputVector_norm (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    ‖qmaOutputVector c hc psi‖ = ‖psi‖ := by
  rw [qmaOutputVector,qmaApplyMatrix_norm _ (qmaCircuitMatrix_gram c hc),qmaInputVector_norm]

theorem qmaAcceptance_projection (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance c hc psi =
      ‖qmaMask (fun s => s (Fin.last c.work) = 1) (qmaOutputVector c hc psi)‖^2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s (Fin.last c.work) = 1 <;>
    simp [qmaMask_apply,hs,qmaOutputVector,qmaApplyMatrix,qmaInputVector,Complex.sq_norm]

theorem qmaRejectVector_square (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    ‖qmaRejectVector c hc psi‖^2 = ‖psi‖^2-qmaAcceptance c hc psi := by
  have h := qmaMask_complement_square (fun s => s (Fin.last c.work) = 1)
    (qmaOutputVector c hc psi)
  rw [←qmaAcceptance_projection,qmaOutputVector_norm] at h
  change qmaAcceptance c hc psi+‖qmaRejectVector c hc psi‖^2 = ‖psi‖^2 at h
  linarith

theorem qmaRejectVector_of_accept (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) : ‖qmaRejectVector c hc psi‖^2 ≤ 1/3 := by
  rw [qmaRejectVector_square,hpsi]
  linarith

theorem qmaRejectVector_of_sound (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : qmaAcceptance c hc psi ≤ 1/3) : 2/3 ≤ ‖qmaRejectVector c hc psi‖^2 := by
  rw [qmaRejectVector_square,hpsi]
  linarith

theorem qmaApplyMatrix_smul {n : ℕ}
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (a : ℂ) (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    qmaApplyMatrix M (a • u) = a • qmaApplyMatrix M u := by
  ext s
  change (M.mulVec (a • (fun s => u s))) s = (a • M.mulVec (fun s => u s)) s
  rw [Matrix.mulVec_smul]

theorem qmaInputVector_smul (c : QMACircuit) (hc : c.WellFormed)
    (a : ℂ) (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaInputVector c hc (a • psi) = a • qmaInputVector c hc psi := by
  classical
  ext s
  by_cases hs : ∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0
  · simp [qmaInputVector,qmaInitialState]
  · simp [qmaInputVector,qmaInitialState,hs]

theorem qmaRejectVector_smul (c : QMACircuit) (hc : c.WellFormed)
    (a : ℂ) (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaRejectVector c hc (a • psi) = a • qmaRejectVector c hc psi := by
  rw [qmaRejectVector,qmaOutputVector,qmaInputVector_smul,qmaApplyMatrix_smul,map_smul]
  rfl

end ContinuumCoulomb

end

end OAI
