import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUnaryForm

namespace OAI

/-! The local endpoint penalties dominate the finite history penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaInputMarker (c : QMACircuit) : Fin (c.gates.length+2) := ⟨1,by omega⟩
def qmaOutputMarker (c : QMACircuit) : Fin (c.gates.length+2) := ⟨c.gates.length,by omega⟩

def qmaUnaryInputEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ s : SourceSpinBasis (c.gates.length+2),
    if s (qmaInputMarker c) = 0 then ∑ a, qmaAncillaCount c a*Complex.normSq (u (s,a)) else 0

def qmaUnaryOutputEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  ∑ s : SourceSpinBasis (c.gates.length+2), if s (qmaOutputMarker c) = 1 then
    ∑ a : SourceSpinBasis (c.work+1), if a (Fin.last c.work) ≠ 1 then
      Complex.normSq (u (s,a)) else 0 else 0

def qmaUnaryEnergy (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) : ℝ :=
  qmaUnaryClockEnergy c u+qmaUnaryOutputEnergy c u+7*qmaUnaryInputEnergy c u+
    8*c.gates.length*qmaUnaryPropagationEnergy c u

theorem qmaInitialCountDiagonal_sum (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ))) u =
      ∑ a : SourceSpinBasis (c.work+1), qmaAncillaCount c a*Complex.normSq (u (0,a)) := by
  rw [qmaQuadratic_diagonal_real]
  simp [qmaInitialCountDiagonal,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel]

theorem qmaOutputPenalty_sum (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaOutputPenalty c (qmaHistoryFromVector c u) =
      ∑ a : SourceSpinBasis (c.work+1), if a (Fin.last c.work) ≠ 1 then
        Complex.normSq (u (Fin.last c.gates.length,a)) else 0 := by
  unfold qmaOutputPenalty
  have hslice : qmaHistoryFromVector c u c.gates.length =
      WithLp.toLp 2 (fun a => u (Fin.last c.gates.length,a)) := by
    ext a
    exact qmaHistoryFromVector_fin c u (Fin.last c.gates.length) a
  rw [hslice,EuclideanSpace.norm_sq_eq]
  simp [qmaMask_apply,apply_ite,Complex.sq_norm]

theorem qmaUnaryInputEnergy_valid_le (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ)))
      (qmaUnaryRestrict c u) ≤ qmaUnaryInputEnergy c u := by
  rw [qmaInitialCountDiagonal_sum]
  have hm : qmaHistoryClock c.gates.length 0 (qmaInputMarker c) = 0 := by
    simp [qmaHistoryClock,qmaUnaryClock,qmaInputMarker]
  have h := Finset.single_le_sum
    (f := fun s : SourceSpinBasis (c.gates.length+2) =>
      if s (qmaInputMarker c) = 0 then ∑ a, qmaAncillaCount c a*Complex.normSq (u (s,a)) else 0)
    (s := Finset.univ) (a := qmaHistoryClock c.gates.length 0)
    (by intro s _; split
        · exact Finset.sum_nonneg (fun a _ => mul_nonneg (qmaAncillaCount_nonneg c a) (Complex.normSq_nonneg _))
        · exact le_rfl) (Finset.mem_univ _)
  simpa only [ite_eq_left hm,qmaUnaryRestrict,qmaUnaryInputEnergy] using h

theorem qmaUnaryOutputEnergy_valid_le (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaOutputPenalty c (qmaHistoryFromVector c (qmaUnaryRestrict c u)) ≤ qmaUnaryOutputEnergy c u := by
  rw [qmaOutputPenalty_sum]
  have hm : qmaHistoryClock c.gates.length (Fin.last c.gates.length) (qmaOutputMarker c) = 1 := by
    simp [qmaHistoryClock,qmaUnaryClock,qmaOutputMarker]
  have h := Finset.single_le_sum
    (f := fun s : SourceSpinBasis (c.gates.length+2) =>
      if s (qmaOutputMarker c) = 1 then
        ∑ a : SourceSpinBasis (c.work+1), if a (Fin.last c.work) ≠ 1 then
          Complex.normSq (u (s,a)) else 0 else 0)
    (s := Finset.univ) (a := qmaHistoryClock c.gates.length (Fin.last c.gates.length))
    (by intro s _; split
        · apply Finset.sum_nonneg
          intro a _
          split
          · exact Complex.normSq_nonneg _
          · exact le_rfl
        · exact le_rfl) (Finset.mem_univ _)
  simpa only [ite_eq_left hm,qmaUnaryRestrict,qmaUnaryOutputEnergy] using h

theorem qmaUnaryEnergy_restriction (c : QMACircuit) (u : QMAUnaryBasis c → ℂ) :
    qmaQuadratic (qmaCountedHistoryHamiltonian c) (qmaUnaryRestrict c u)+
      qmaUnaryClockEnergy c u ≤ qmaUnaryEnergy c u := by
  rw [qmaCountedHistoryHamiltonian_form]
  have hi := qmaUnaryInputEnergy_valid_le c u
  have ho := qmaUnaryOutputEnergy_valid_le c u
  have hp := mul_le_mul_of_nonneg_left (qmaUnaryPropagationEnergy_valid_le c u)
    (by positivity : 0 ≤ 8*(c.gates.length:ℝ))
  unfold qmaUnaryEnergy
  linarith

end ContinuumCoulomb

end

end OAI
