import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTransferSweep

namespace OAI

/-! A concrete schedule of initialization checks, one at each qubit's first use. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaFirstUse (c : QMACircuit) (i : Fin (c.work+1)) : ℕ :=
  c.gates.findIdx (fun g => decide (i ∈ qmaGateSites c.work g))

theorem qmaFirstUse_le (c : QMACircuit) (i : Fin (c.work+1)) :
    qmaFirstUse c i ≤ c.gates.length := List.findIdx_le_length

theorem qmaFirstUse_untouched (c : QMACircuit) (i : Fin (c.work+1)) :
    ∀ g ∈ c.gates.take (qmaFirstUse c i), i ∉ qmaGateSites c.work g := by
  intro g hg
  have h := List.false_of_mem_take_findIdx hg
  exact of_decide_eq_false h

theorem qmaFirstUse_input_preserved (c : QMACircuit) (hc : c.WellFormed)
    (i : Fin (c.work+1)) (u : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c (qmaFirstUse c i)) u)‖ =
      ‖qmaMask (qmaInputCheck c i) u‖ :=
  qmaInputCheck_prefix_untouched c hc i (qmaFirstUse c i) (qmaFirstUse_untouched c i) u

theorem qmaFirstUse_history_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    2*qmaHistoryMass c u ≤
      5*(c.gates.length+1:ℝ)*qmaDistributedHistoryEnergy c (qmaFirstUse c) u :=
  qmaDistributedHistoryEnergy_sound_untouched c hc (qmaFirstUse c)
    (qmaFirstUse_le c) (qmaFirstUse_untouched c) hsound u

end ContinuumCoulomb

end

end OAI
