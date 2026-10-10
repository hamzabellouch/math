import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryMatrix

namespace OAI

/-! The finite matrix is exactly the quadratic history form. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_clock_mask (c : QMACircuit) (t : Fin (c.gates.length+1))
    (p : SourceSpinBasis (c.work+1) → Prop) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (fun k : QMAHistoryBasis c =>
      if k.1 = t ∧ p k.2 then (1:ℂ) else 0)) u =
      ‖qmaMask p (qmaHistoryFromVector c u t.val)‖^2 := by
  have h := qmaQuadratic_diagonal_mask (fun k : QMAHistoryBasis c => k.1 = t ∧ p k.2) u
  have hm : qmaQuadratic (Matrix.diagonal (fun k : QMAHistoryBasis c =>
      if k.1 = t ∧ p k.2 then (1:ℂ) else 0)) u =
      ∑ k : QMAHistoryBasis c, if k.1 = t ∧ p k.2 then Complex.normSq (u k) else 0 := by
    convert h using 1
    · congr 2
      funext k
      split <;> simp_all
    · apply Finset.sum_congr rfl
      intro k _
      split <;> simp_all
  rw [hm,EuclideanSpace.norm_sq_eq]
  simp [Fintype.sum_prod_type,ite_and,Finset.sum_ite_irrel,Complex.sq_norm,apply_ite]

theorem qmaPropagationMatrix_mulVec (c : QMACircuit) (u : QMAHistoryBasis c → ℂ)
    (t : Fin c.gates.length) (s : SourceSpinBasis (c.work+1)) :
    (qmaPropagationMatrix c).mulVec u (t,s) =
      (qmaHistoryFromVector c u (t.val+1)-qmaApplyMatrix (qmaStepMatrix c t.val)
        (qmaHistoryFromVector c u t.val)) s := by
  rw [qmaPropagationMatrix,LinearMap.toMatrix'_mulVec]
  simp [qmaPropagationMap,qmaHistoryFromVector,qmaClockIndex,qmaApplyMatrix,
]

theorem qmaPropagationMatrix_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic ((qmaPropagationMatrix c).conjTranspose*qmaPropagationMatrix c) u =
      qmaPropagationEnergy c (qmaHistoryFromVector c u) := by
  rw [qmaQuadratic_gram]
  unfold qmaPropagationEnergy
  rw [←Fin.sum_univ_eq_sum_range,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  rw [EuclideanSpace.norm_sq_eq]
  simp only [qmaPropagationMatrix_mulVec,Complex.sq_norm]

theorem qmaInitialDiagonal_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (qmaInitialDiagonal c)) u =
      qmaInputPenalty c (qmaHistoryFromVector c u) := by
  have he : qmaInitialDiagonal c = fun k : QMAHistoryBasis c =>
      if k.1 = (0 : Fin (c.gates.length+1)) ∧ ¬QMAAncillaZero c k.2 then (1:ℂ) else 0 := by
    funext k
    simp only [qmaInitialDiagonal,Fin.val_eq_zero_iff]
  rw [he]
  convert qmaQuadratic_clock_mask c 0 (fun s => ¬QMAAncillaZero c s) u using 1
  · congr 2
    funext k
    split <;> simp_all
  · rfl

theorem qmaFinalDiagonal_energy (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (Matrix.diagonal (qmaFinalDiagonal c)) u =
      qmaOutputPenalty c (qmaHistoryFromVector c u) := by
  have he : qmaFinalDiagonal c = fun k : QMAHistoryBasis c =>
      if k.1 = Fin.last c.gates.length ∧ k.2 (Fin.last c.work) ≠ 1 then (1:ℂ) else 0 := by
    funext k
    simp [qmaFinalDiagonal,Fin.ext_iff]
  rw [he]
  convert qmaQuadratic_clock_mask c (Fin.last c.gates.length)
    (fun s => s (Fin.last c.work) ≠ 1) u using 1
  · congr 2
    funext k
    split <;> simp_all
  · rfl

theorem qmaHistoryHamiltonian_form (c : QMACircuit) (u : QMAHistoryBasis c → ℂ) :
    qmaQuadratic (qmaHistoryHamiltonian c) u =
      qmaHistoryEnergy c (qmaHistoryFromVector c u) := by
  unfold qmaHistoryHamiltonian
  rw [qmaQuadratic_add,qmaQuadratic_add]
  have hs : (8*c.gates.length:ℂ) = ((8*(c.gates.length:ℝ):ℝ):ℂ) := by push_cast; rfl
  rw [hs,qmaQuadratic_smul]
  have h7 : (7:ℂ) = ((7:ℝ):ℂ) := by norm_num
  rw [h7,qmaQuadratic_smul]
  rw [qmaInitialDiagonal_energy,qmaFinalDiagonal_energy,qmaPropagationMatrix_energy]
  rfl

end ContinuumCoulomb

end

end OAI
