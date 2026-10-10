import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAncillaCount

namespace OAI

/-! The history input energy as a sum of individual ancilla projectors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_diagonal_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (u : ι → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun i => (d i : ℂ))) u =
      ∑ i, d i*Complex.normSq (u i) := by
  simp only [qmaQuadratic,dotProduct,Matrix.mulVec_diagonal,Complex.re_sum,Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re,Complex.normSq_apply]
  ring

def qmaInitialCountDiagonal (c : QMACircuit) (k : QMAHistoryBasis c) : ℝ :=
  if k.1.val = 0 then qmaAncillaCount c k.2 else 0

theorem qmaInitialCountDiagonal_ge (c : QMACircuit) (k : QMAHistoryBasis c) :
    (if k.1.val = 0 ∧ ¬QMAAncillaZero c k.2 then (1:ℝ) else 0) ≤
      qmaInitialCountDiagonal c k := by
  by_cases ht : k.1.val = 0
  · by_cases hs : QMAAncillaZero c k.2
    · simpa [qmaInitialCountDiagonal,ht,hs] using qmaAncillaCount_nonneg c k.2
    · simpa [qmaInitialCountDiagonal,ht,hs] using qmaAncillaCount_one_le c k.2 hs
  · simp [qmaInitialCountDiagonal,ht]

theorem qmaInitialCountDiagonal_energy_ge (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (qmaInitialDiagonal c)) u ≤
      qmaQuadratic (Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ))) u := by
  have hleft : qmaQuadratic (Matrix.diagonal (qmaInitialDiagonal c)) u =
      ∑ k : QMAHistoryBasis c,
        (if k.1.val = 0 ∧ ¬QMAAncillaZero c k.2 then (1:ℝ) else 0)*Complex.normSq (u k) := by
    convert qmaQuadratic_diagonal_real (fun k : QMAHistoryBasis c =>
      if k.1.val = 0 ∧ ¬QMAAncillaZero c k.2 then (1:ℝ) else 0) u using 1
    congr 2
    funext k
    by_cases hk : k.1.val = 0 ∧ ¬QMAAncillaZero c k.2
    · simp only [qmaInitialDiagonal,ite_eq_left hk,Complex.ofReal_one]
    · simp only [qmaInitialDiagonal,ite_eq_right hk,Complex.ofReal_zero]
  rw [hleft,qmaQuadratic_diagonal_real]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_right (qmaInitialCountDiagonal_ge c k) (Complex.normSq_nonneg _)

theorem qmaInitialCountDiagonal_ideal_zero (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaQuadratic (Matrix.diagonal (fun k => (qmaInitialCountDiagonal c k : ℂ)))
      (fun k => qmaHistoryVector c (qmaIdealHistory c hc psi) k) = 0 := by
  rw [qmaQuadratic_diagonal_real]
  apply Finset.sum_eq_zero
  intro k _
  by_cases ht : k.1.val = 0
  · by_cases hs : QMAAncillaZero c k.2
    · simp [qmaInitialCountDiagonal,ht,qmaAncillaCount_zero c k.2 hs]
    · have hs' : ¬∀ i : Fin (c.work+1), c.witness ≤ i.val → k.2 i = 0 := hs
      simp [qmaHistoryVector,qmaIdealHistory,ht,qmaInputVector,qmaInitialState,hs']
  · simp [qmaInitialCountDiagonal,ht]

end ContinuumCoulomb

end

end OAI
