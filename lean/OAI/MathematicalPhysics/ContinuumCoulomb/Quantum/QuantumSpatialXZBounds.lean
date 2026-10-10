import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialXZ
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighbors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialCircuit

namespace OAI

/-! Explicit size, degree and promise bounds for the spatial X/Z Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem QMASpatialXZModel.incidence_bound {A B : ℕ} (M : QMASpatialXZModel A B) (q : M.Q) :
    (Finset.univ.filter (fun e => q ∈ qmaPauliSupport (M.word e))).card ≤ 9*B :=
  qmaGrid_incidence_bound M.cell M.anchor (fun e => qmaPauliSupport (M.word e))
    M.geometry M.termDensity q

theorem QMASpatialXZModel.qubits_bound {A B : ℕ} (M : QMASpatialXZModel A B) :
    M.toQMAXZModel.qubits ≤ (M.rows+1)*(M.width+1)*A :=
  qmaGrid_density_card M.cell M.qubitDensity

theorem QMASpatialXZModel.terms_bound {A B : ℕ} (M : QMASpatialXZModel A B) :
    M.toQMAXZModel.terms ≤ (M.rows+1)*(M.width+1)*B :=
  qmaGrid_density_card M.anchor M.termDensity

theorem qmaCircuit_spatial_XZ (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialXZModel
        (45+1077940224*64+80*(7516192768*64)) (448*(7516192768*64)),
      G.rows = (qmaNearestCircuit c).gates.length ∧ G.width = c.work ∧
      (∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        2/3 ≤ qmaAcceptance c hc psi →
        G.toQMAXZModel.energy ≤ 1/(3*((qmaSparseCircuit c).gates.length+1:ℝ))+1/N) ∧
      ((∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        qmaAcceptance c hc psi ≤ 1/3) →
        2/(5*((qmaSparseCircuit c).gates.length+1:ℝ))-1/N ≤ G.toQMAXZModel.energy) := by
  have h2N : 1 ≤ 2*N := by linarith
  obtain ⟨M,hr,hw,hyes,hno⟩ := qmaCircuit_spatial_two_local c hc hT hne h2N
  obtain ⟨G,he,hGr,hGw⟩ := M.toXZ h2N
  refine ⟨G,hGr.trans hr,hGw.trans hw,?_,?_⟩
  · intro psi hpsi ha
    have h := hyes psi hpsi ha
    have hle := (abs_le.mp he).2
    have hsum : 1/(2*N)+1/(2*N) = 1/N := by ring
    linarith
  · intro ha
    have h := hno ha
    have hle := (abs_le.mp he).1
    have hsum : 1/(2*N)+1/(2*N) = 1/N := by ring
    linarith

end ContinuumCoulomb

end

end OAI
