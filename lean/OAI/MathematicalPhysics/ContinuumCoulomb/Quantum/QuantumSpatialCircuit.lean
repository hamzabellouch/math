import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialGadgets

namespace OAI

/-! A single spatial two-local Hamiltonian carries both verifier promise cases. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaCircuit_spatial_two_local (c : QMACircuit) (hc : c.WellFormed)
    (hT : 0 < (qmaSparseCircuit c).gates.length)
    (hne : (qmaNearestCircuit c).gates ≠ []) {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialModel 2 (45+1077940224*64) (7516192768*64),
      G.rows = (qmaNearestCircuit c).gates.length ∧ G.width = c.work ∧
      (∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        2/3 ≤ qmaAcceptance c hc psi →
        G.toQMARealLocalModel.energy ≤ 1/(3*((qmaSparseCircuit c).gates.length+1:ℝ))+1/N) ∧
      ((∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness), ‖psi‖ = 1 →
        qmaAcceptance c hc psi ≤ 1/3) →
        2/(5*((qmaSparseCircuit c).gates.length+1:ℝ))-1/N ≤ G.toQMARealLocalModel.energy) := by
  let M := qmaSpatialHistoryModel c hc hT hne
  obtain ⟨G,hG,hr,hw⟩ := M.six_to_two hN
  refine ⟨G,hr,hw,?_,?_⟩
  · intro psi hpsi hacc
    have ha : 2/3 ≤ qmaAcceptance (qmaSparseCircuit c) (qmaSparseCircuit_wellFormed c hc) psi := by
      rwa [qmaSparseCircuit_acceptance]
    have hm := qmaOrderedHistoryModel_yes (qmaSparseCircuit c) hT
      (qmaSparseCircuit_wellFormed c hc) psi hpsi ha
    change (qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy ≤ _ at hm
    change |G.toQMARealLocalModel.energy-(qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy| ≤ 1/N at hG
    have he := (abs_le.mp hG).2
    linarith
  · intro hsound
    have ha : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis (qmaSparseCircuit c).witness), ‖psi‖ = 1 →
        qmaAcceptance (qmaSparseCircuit c) (qmaSparseCircuit_wellFormed c hc) psi ≤ 1/3 := by
      intro psi hpsi
      rw [qmaSparseCircuit_acceptance]
      exact hsound psi hpsi
    have hm := qmaOrderedHistoryModel_no (qmaSparseCircuit c) hT
      (qmaSparseCircuit_wellFormed c hc) ha
    change _ ≤ (qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy at hm
    change |G.toQMARealLocalModel.energy-(qmaOrderedHistoryModel (qmaSparseCircuit c) hT).energy| ≤ 1/N at hG
    have he := (abs_le.mp hG).1
    linarith

end ContinuumCoulomb

end

end OAI
