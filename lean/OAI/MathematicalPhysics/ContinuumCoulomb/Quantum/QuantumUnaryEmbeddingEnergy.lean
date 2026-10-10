import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryEmbedding

namespace OAI

/-! Exact energy preservation of the accepting unary-clock embedding. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

theorem qmaUnaryExtend_weighted_sum (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (w : SourceSpinBasis (c.gates.length+2) → SourceSpinBasis (c.work+1) → ℝ) :
    (∑ s : SourceSpinBasis (c.gates.length+2), ∑ a,
      w s a*Complex.normSq (qmaUnaryExtend c u (s,a))) =
    ∑ t : Fin (c.gates.length+1), ∑ a,
      w (qmaHistoryClock c.gates.length t) a*Complex.normSq (u (t,a)) := by
  have he := qmaClock_sector_sum c.gates.length (fun s =>
    ∑ a, w s a*Complex.normSq (qmaUnaryExtend c u (s,a)))
  have hz : (∑ s : SourceSpinBasis (c.gates.length+2),
      if QMALegalClock c.gates.length s then 0 else
        ∑ a, w s a*Complex.normSq (qmaUnaryExtend c u (s,a))) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : QMALegalClock c.gates.length s
    · exact ite_eq_left hs
    · simp only [ite_eq_right hs,qmaUnaryExtend_zero c u s _ hs,
        Complex.normSq_zero,mul_zero,Finset.sum_const_zero]
  rw [hz,add_zero] at he
  simpa only [qmaUnaryExtend_valid] using he

theorem qmaHistoryClock_input_marker (c : QMACircuit) (t : Fin (c.gates.length+1)) :
    qmaHistoryClock c.gates.length t (qmaInputMarker c) = 0 ↔ t = 0 := by
  by_cases ht : t = 0
  · subst t
    simp [qmaHistoryClock,qmaUnaryClock,qmaInputMarker]
  · have hn : t.val ≠ 0 := fun h => ht (Fin.ext h)
    have hh : 1 < t.val+1 := by omega
    simp [qmaHistoryClock,qmaUnaryClock,qmaInputMarker,hh,ht]

theorem qmaHistoryClock_output_marker (c : QMACircuit) (t : Fin (c.gates.length+1)) :
    qmaHistoryClock c.gates.length t (qmaOutputMarker c) = 1 ↔ t = Fin.last c.gates.length := by
  by_cases ht : t = Fin.last c.gates.length
  · subst t
    simp [qmaHistoryClock,qmaUnaryClock,qmaOutputMarker]
  · have hn : t.val ≠ c.gates.length := fun h => ht (Fin.ext h)
    have hh : ¬c.gates.length < t.val+1 := by omega
    simp [qmaHistoryClock,qmaUnaryClock,qmaOutputMarker,hh,ht]

theorem qmaUnaryExtend_input_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryInputEnergy c (qmaUnaryExtend c u) =
      qmaQuadratic (Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ))) u := by
  have h := qmaUnaryExtend_weighted_sum c u (fun s a =>
    if s (qmaInputMarker c) = 0 then qmaAncillaCount c a else 0)
  simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
    qmaHistoryClock_input_marker] at h
  rw [qmaInitialCountDiagonal_sum]
  simpa only [qmaUnaryInputEnergy,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h

theorem qmaUnaryExtend_output_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryOutputEnergy c (qmaUnaryExtend c u) =
      qmaOutputPenalty c (qmaHistoryFromVector c u) := by
  have h := qmaUnaryExtend_weighted_sum c u (fun s a =>
    if s (qmaOutputMarker c) = 1 ∧ a (Fin.last c.work) ≠ 1 then 1 else 0)
  simp only [ite_mul,one_mul,zero_mul,ite_and,Finset.sum_ite_irrel,
    Finset.sum_const_zero,qmaHistoryClock_output_marker] at h
  rw [qmaOutputPenalty_sum]
  simpa only [qmaUnaryOutputEnergy,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h

theorem qmaUnaryExtend_propagation_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryPropagationEnergy c (qmaUnaryExtend c u) =
      qmaPropagationEnergy c (qmaHistoryFromVector c u) := by
  rw [←qmaPropagationMatrix_energy,qmaQuadratic_gram,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  have hz : QMAClockGuard c.gates.length t (qmaHistoryClock c.gates.length t.castSucc) ∧
      qmaHistoryClock c.gates.length t.castSucc (qmaClockMiddle c.gates.length t) = 0 :=
    ⟨qmaClock_step_guard _ _,qmaClock_step_zero _ _⟩
  calc
    _ = (if QMAClockGuard c.gates.length t (qmaHistoryClock c.gates.length t.castSucc) ∧
        qmaHistoryClock c.gates.length t.castSucc (qmaClockMiddle c.gates.length t) = 0 then
        ∑ a, Complex.normSq (qmaUnaryResidual c (qmaUnaryExtend c u) t
          (qmaHistoryClock c.gates.length t.castSucc) a) else 0) := by
      apply Finset.sum_eq_single (qmaHistoryClock c.gates.length t.castSucc)
      · intro s _ hne
        by_cases ha : QMAClockGuard c.gates.length t s ∧ s (qmaClockMiddle c.gates.length t) = 0
        · rw [ite_eq_left ha]
          have hs : ¬QMALegalClock c.gates.length s := by
            intro hs
            exact hne (qmaClock_step_legal_before _ _ _ ha.1 ha.2 hs).symm
          apply Finset.sum_eq_zero
          intro a _
          rw [qmaUnaryResidual_extend_invalid c u t s ha.1 ha.2 hs a,Complex.normSq_zero]
        · exact ite_eq_right ha
      · simp
    _ = _ := by simp only [ite_eq_left hz,qmaUnaryResidual_valid,qmaUnaryRestrict_extend]

theorem qmaUnaryExtend_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaUnaryEnergy c (qmaUnaryExtend c u) = qmaQuadratic (qmaCountedHistoryHamiltonian c) u := by
  rw [qmaUnaryEnergy,qmaUnaryExtend_clock_energy,qmaUnaryExtend_input_energy,
    qmaUnaryExtend_output_energy,qmaUnaryExtend_propagation_energy,
    qmaCountedHistoryHamiltonian_form,zero_add]

end ContinuumCoulomb

end

end OAI
