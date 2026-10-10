import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistory
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumInputProjection
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.ClockWeightedBound

namespace OAI

/-! A quantitative circuit-history promise gap, for all history vectors. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def qmaHistoryMass (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ∑ t ∈ Finset.range (c.gates.length+1), ‖u t‖^2

def qmaInputPenalty (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ‖qmaMask (fun s => ¬QMAAncillaZero c s) (u 0)‖^2

def qmaOutputPenalty (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ‖qmaMask (fun s => s (Fin.last c.work) ≠ 1) (u c.gates.length)‖^2

def qmaHistoryEnergy (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  qmaOutputPenalty c u+7*qmaInputPenalty c u+
    8*c.gates.length*qmaPropagationEnergy c u

theorem qma_history_legal_endpoint_bound (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c)
      (qmaMask (QMAAncillaZero c) (u 0))‖^2 ≤
      2*c.gates.length*qmaPropagationEnergy c u+2*qmaInputPenalty c u := by
  let v := qmaMask (QMAAncillaZero c) (u 0)
  have ha := qma_history_anchor_bound c hc u c.gates.length le_rfl
  rw [qmaPrefixMatrix_length] at ha
  have hb : ‖qmaApplyMatrix (qmaCircuitMatrix c) (u 0-v)‖^2 = qmaInputPenalty c u := by
    rw [qmaApplyMatrix_norm _ (qmaCircuitMatrix_gram c hc)]
    dsimp [v]
    rw [qmaMask_sub_self]
    rfl
  have he : (u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c) (u 0))+
      qmaApplyMatrix (qmaCircuitMatrix c) (u 0-v) =
      u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c) v := by
    rw [qmaApplyMatrix_sub]
    abel
  have h := norm_add_sq_two
    (u c.gates.length-qmaApplyMatrix (qmaCircuitMatrix c) (u 0))
    (qmaApplyMatrix (qmaCircuitMatrix c) (u 0-v))
  rw [he,hb] at h
  exact h.trans (by linarith)

theorem qma_history_output_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    ‖qmaMask (QMAAncillaZero c) (u 0)‖^2 ≤
      2*qmaOutputPenalty c u+12*c.gates.length*qmaPropagationEnergy c u+
        12*qmaInputPenalty c u := by
  let p := fun s : SourceSpinBasis (c.work+1) => s (Fin.last c.work) ≠ 1
  let v := qmaMask (QMAAncillaZero c) (u 0)
  let w := qmaApplyMatrix (qmaCircuitMatrix c) v
  have hs := qmaRejectVector_sound_all c hc hsound (qmaExtractWitness c (u 0))
  rw [qmaExtractWitness_norm c hc] at hs
  have hr : qmaRejectVector c hc (qmaExtractWitness c (u 0)) = qmaMask p w := by
    rw [qmaRejectVector,qmaOutputVector,qmaInputVector_extract]
  rw [hr] at hs
  have hd : ‖qmaMask p w-qmaMask p (u c.gates.length)‖^2 ≤
      2*c.gates.length*qmaPropagationEnergy c u+2*qmaInputPenalty c u := by
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (qmaMask_sub_norm_le p w (u c.gates.length)) 2
    rw [norm_sub_rev w] at h
    exact h.trans (qma_history_legal_endpoint_bound c hc u)
  have ht := norm_add_sq_three (qmaMask p (u c.gates.length))
    (qmaMask p w-qmaMask p (u c.gates.length))
  have he : qmaMask p (u c.gates.length)+
      (qmaMask p w-qmaMask p (u c.gates.length)) = qmaMask p w := by abel
  rw [he] at ht
  change 3*‖qmaMask p w‖^2 ≤ 4*qmaOutputPenalty c u+
    12*‖qmaMask p w-qmaMask p (u c.gates.length)‖^2 at ht
  nlinarith

theorem qma_history_energy_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    2*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaHistoryEnergy c u := by
  have hm := clock_path_weighted_mass_bound (qmaHistoryGauge c u) c.gates.length
  simp only [qmaHistoryGauge_norm c hc u,qmaHistoryGauge_energy c hc u] at hm
  change 4*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*‖u 0‖^2+
    20*c.gates.length*(c.gates.length+1:ℝ)*qmaPropagationEnergy c u at hm
  have hsplit := qmaMask_complement_square (QMAAncillaZero c) (u 0)
  change ‖qmaMask (QMAAncillaZero c) (u 0)‖^2+qmaInputPenalty c u = ‖u 0‖^2 at hsplit
  have hout := qma_history_output_sound c hc hsound u
  have hx := mul_le_mul_of_nonneg_left hout
    (by positivity : 0 ≤ 5*(c.gates.length+1:ℝ))
  have hi : 0 ≤ (c.gates.length+1:ℝ)*qmaInputPenalty c u := by
    unfold qmaInputPenalty
    positivity
  unfold qmaHistoryEnergy
  nlinarith

end ContinuumCoulomb

end

end OAI
