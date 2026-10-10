import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryEnergy

namespace OAI

/-! Explicit accepting histories and their exact mass and energy. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def qmaIdealHistory (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness))
    (t : ℕ) : EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaApplyMatrix (qmaPrefixMatrix c t) (qmaInputVector c hc psi)

theorem qmaIdealHistory_mass (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaHistoryMass c (qmaIdealHistory c hc psi) = (c.gates.length+1:ℝ)*‖psi‖^2 := by
  simp [qmaHistoryMass,qmaIdealHistory,
    qmaApplyMatrix_norm _ (qmaPrefixMatrix_gram c hc _),qmaInputVector_norm]

theorem qmaIdealHistory_propagation (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaPropagationEnergy c (qmaIdealHistory c hc psi) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  simp only [qmaIdealHistory,qmaPrefixMatrix_succ c t (Finset.mem_range.mp ht),
    qmaApplyMatrix_mul,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]

theorem qmaIdealHistory_input (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaInputPenalty c (qmaIdealHistory c hc psi) = 0 := by
  have he : qmaMask (fun s => ¬QMAAncillaZero c s) (qmaInputVector c hc psi) = 0 := by
    classical
    ext s
    by_cases hs : QMAAncillaZero c s
    · simp [hs]
    · have hs' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val → s i = 0 := hs
      simp [hs,qmaInputVector,qmaInitialState,hs']
  simp only [qmaInputPenalty,qmaIdealHistory,qmaPrefixMatrix_zero,qmaApplyMatrix_one,
    he,norm_zero,zero_pow (by decide : 2 ≠ 0)]

theorem qmaIdealHistory_energy (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaHistoryEnergy c (qmaIdealHistory c hc psi) = ‖qmaRejectVector c hc psi‖^2 := by
  rw [qmaHistoryEnergy,qmaIdealHistory_input,qmaIdealHistory_propagation]
  simp only [mul_zero,add_zero,qmaOutputPenalty,qmaIdealHistory,qmaPrefixMatrix_length,
    qmaRejectVector,qmaOutputVector]

theorem qma_history_accepting_witness (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1)),
      0 < qmaHistoryMass c u ∧
      3*(c.gates.length+1:ℝ)*qmaHistoryEnergy c u ≤ qmaHistoryMass c u := by
  refine ⟨qmaIdealHistory c hc psi,?_,?_⟩
  · rw [qmaIdealHistory_mass,hpsi]
    positivity
  · rw [qmaIdealHistory_mass,qmaIdealHistory_energy,hpsi]
    have h := mul_le_mul_of_nonneg_left (qmaRejectVector_of_accept c hc psi hpsi hacc)
      (by positivity : 0 ≤ 3*(c.gates.length+1:ℝ))
    nlinarith

end ContinuumCoulomb

end

end OAI
