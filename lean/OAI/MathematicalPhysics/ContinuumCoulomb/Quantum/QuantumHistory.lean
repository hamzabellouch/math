import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrefix
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.ClockPathBound

namespace OAI

/-! Quantitative propagation for the actual H,T,CNOT circuit history. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open Matrix

def qmaHistoryGauge (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) (t : ℕ) :
    EuclideanSpace ℂ (SourceSpinBasis (c.work+1)) :=
  qmaApplyMatrix (qmaPrefixMatrix c t).conjTranspose (u t)

def qmaPropagationEnergy (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ∑ t ∈ Finset.range c.gates.length, ‖u (t+1)-qmaApplyMatrix (qmaStepMatrix c t) (u t)‖^2

theorem qmaHistoryGauge_norm (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) (t : ℕ) :
    ‖qmaHistoryGauge c u t‖ = ‖u t‖ := by
  apply qmaApplyMatrix_norm
  simpa only [Matrix.conjTranspose_conjTranspose] using qmaPrefixMatrix_cogram c hc t

theorem qmaHistoryGauge_step (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1)))
    (t : ℕ) (ht : t < c.gates.length) :
    qmaHistoryGauge c u (t+1)-qmaHistoryGauge c u t =
      qmaApplyMatrix (qmaPrefixMatrix c (t+1)).conjTranspose
        (u (t+1)-qmaApplyMatrix (qmaStepMatrix c t) (u t)) := by
  have hp : (qmaPrefixMatrix c (t+1)).conjTranspose*qmaStepMatrix c t =
      (qmaPrefixMatrix c t).conjTranspose := by
    rw [qmaPrefixMatrix_succ c t ht,Matrix.conjTranspose_mul,mul_assoc,
      qmaStepMatrix_gram c hc t ht,mul_one]
  rw [qmaApplyMatrix_sub,←qmaApplyMatrix_mul,hp]
  rfl

theorem qmaHistoryGauge_energy (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    clockPathEnergy (qmaHistoryGauge c u) c.gates.length = qmaPropagationEnergy c u := by
  apply Finset.sum_congr rfl
  intro t ht
  rw [qmaHistoryGauge_step c hc u t (Finset.mem_range.mp ht),qmaApplyMatrix_norm]
  simpa only [Matrix.conjTranspose_conjTranspose] using qmaPrefixMatrix_cogram c hc (t+1)

theorem qma_history_anchor_bound (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) (t : ℕ)
    (ht : t ≤ c.gates.length) :
    ‖u t-qmaApplyMatrix (qmaPrefixMatrix c t) (u 0)‖^2 ≤
      (c.gates.length:ℝ)*qmaPropagationEnergy c u := by
  have heq : qmaApplyMatrix (qmaPrefixMatrix c t)
      (qmaHistoryGauge c u t-qmaHistoryGauge c u 0) =
      u t-qmaApplyMatrix (qmaPrefixMatrix c t) (u 0) := by
    rw [qmaApplyMatrix_sub]
    change qmaApplyMatrix (qmaPrefixMatrix c t)
      (qmaApplyMatrix (qmaPrefixMatrix c t).conjTranspose (u t)) -
      qmaApplyMatrix (qmaPrefixMatrix c t)
      (qmaApplyMatrix (qmaPrefixMatrix c 0).conjTranspose (u 0)) = _
    rw [←qmaApplyMatrix_mul,qmaPrefixMatrix_cogram c hc t]
    simp
  have h := clock_path_anchor_bound (qmaHistoryGauge c u) c.gates.length t ht
  rw [qmaHistoryGauge_energy c hc u] at h
  rw [←heq,qmaApplyMatrix_norm _ (qmaPrefixMatrix_gram c hc t)]
  exact h

theorem qma_history_mass_bound (c : QMACircuit) (hc : c.WellFormed)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    (∑ t ∈ Finset.range (c.gates.length+1), ‖u t‖^2) ≤
      2*(c.gates.length+1:ℝ)*‖u 0‖^2 +
      2*c.gates.length*(c.gates.length+1:ℝ)*qmaPropagationEnergy c u := by
  have h := clock_path_mass_bound (qmaHistoryGauge c u) c.gates.length
  simpa only [qmaHistoryGauge_norm c hc u,qmaHistoryGauge_energy c hc u] using h

end ContinuumCoulomb

end

end OAI
