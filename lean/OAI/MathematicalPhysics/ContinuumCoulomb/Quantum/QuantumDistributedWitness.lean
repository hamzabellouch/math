import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedClock
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryEmbeddingEnergy

namespace OAI

/-! Accepting histories retain exactly their output energy under distributed checks. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaUnaryExtend_distributed_input (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryDistributedInput c τ (qmaUnaryExtend c u) =
      qmaDistributedInput c (fun i => (τ i).val) (qmaHistoryFromVector c u) := by
  unfold qmaUnaryDistributedInput qmaDistributedInput
  apply Finset.sum_congr rfl
  intro i _
  have h := qmaUnaryExtend_weighted_sum c u (fun s a =>
    if qmaClockAt c.gates.length (τ i) s ∧ qmaInputCheck c i a then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul,ite_and,Finset.sum_ite_irrel,
    Finset.sum_const_zero,qmaClockAt_history] at h
  rw [qmaMask_norm_sq]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  rw [qmaHistoryFromVector_fin]
  simp only [Complex.sq_norm]

theorem qmaInputVector_single_check_zero (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (i : Fin (c.work+1)) :
    qmaMask (qmaInputCheck c i) (qmaInputVector c hc psi) = 0 := by
  ext s
  by_cases hi : qmaInputCheck c i s
  · have hs : ¬∀ j : Fin (c.work+1), c.witness ≤ j.val → s j = 0 := by
      intro h
      exact hi.2 (h i hi.1)
    simp [hi,qmaInputVector,qmaInitialState,hs]
  · simp [hi]

theorem qmaIdealHistory_distributed_input (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaDistributedInput c (fun i => (τ i).val) (qmaIdealHistory c hc psi) = 0 := by
  unfold qmaDistributedInput qmaIdealHistory
  apply Finset.sum_eq_zero
  intro i _
  rw [qmaInputCheck_prefix_untouched c hc i (τ i).val (hi i),
    qmaInputVector_single_check_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]

theorem qmaUnaryExtend_distributed_energy (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryDistributedEnergy c τ (qmaUnaryExtend c u) =
      qmaDistributedHistoryEnergy c (fun i => (τ i).val) (qmaHistoryFromVector c u) := by
  rw [qmaUnaryDistributedEnergy,qmaUnaryExtend_clock_energy,
    qmaUnaryExtend_distributed_input,qmaUnaryExtend_output_energy,
    qmaUnaryExtend_propagation_energy,zero_add]
  rfl

theorem qmaIdealHistory_distributed_energy (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaDistributedHistoryEnergy c (fun i => (τ i).val) (qmaIdealHistory c hc psi) =
      ‖qmaRejectVector c hc psi‖^2 := by
  rw [qmaDistributedHistoryEnergy,qmaIdealHistory_distributed_input c hc τ hi,
    qmaIdealHistory_propagation]
  simp only [mul_zero,add_zero,qmaOutputPenalty,qmaIdealHistory,qmaPrefixMatrix_length,
    qmaRejectVector,qmaOutputVector]

end ContinuumCoulomb

end

end OAI
