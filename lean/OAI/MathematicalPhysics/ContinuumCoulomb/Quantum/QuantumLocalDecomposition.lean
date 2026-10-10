import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPropagationAction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalPenalties

namespace OAI

/-! Exact sum of finite-support terms for the full unary-clock Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaSubmatrix_add {α β γ δ : Type*} (A B : Matrix α β ℂ)
    (f : γ → α) (g : δ → β) : (A+B).submatrix f g = A.submatrix f g+B.submatrix f g := rfl

theorem qmaSubmatrix_smul {α β γ δ : Type*} (z : ℂ) (A : Matrix α β ℂ)
    (f : γ → α) (g : δ → β) : (z • A).submatrix f g = z • A.submatrix f g := rfl

theorem qmaOfReal_ite (p : Prop) [Decidable p] (a b : ℝ) :
    ((if p then a else b : ℝ) : ℂ) = if p then (a:ℂ) else (b:ℂ) := by
  split <;> rfl

def qmaQubitHamiltonian (c : QMACircuit) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  (qmaUnaryHamiltonian c).submatrix (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c)

theorem qmaUnaryPropagationGram_reindex (c : QMACircuit) :
    ((qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
      ∑ t : Fin c.gates.length,
        (qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t := by
  have hs (t : Fin c.gates.length) :
      (qmaPropagationSlice c t).submatrix (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
        qmaLocalPropagationDelta c t := by
    rw [qmaPropagationSlice_eq]
    ext s r
    simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]
  calc
    _ = ∑ t : Fin c.gates.length,
        ((qmaPropagationSlice c t).conjTranspose*qmaPropagationSlice c t).submatrix
          (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) := by
      ext s r
      simp only [qmaUnaryPropagationGram_sum,Matrix.submatrix_apply,Matrix.sum_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [←Matrix.submatrix_mul_equiv _ _ (qmaCircuitQubitSplit c)
        (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c),←Matrix.conjTranspose_submatrix,hs]

theorem qmaUnaryClockDiagonal_reindex (c : QMACircuit) :
    (Matrix.diagonal (fun p => (qmaUnaryClockDiagonal c p : ℂ))).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
      (∑ i : Fin (c.gates.length+1), qmaClockFaultTerm c i)+qmaClockLeftTerm c+qmaClockRightTerm c := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext s r
  by_cases h : s = r
  · subst r
    simp only [Matrix.add_apply,Matrix.sum_apply,qmaClockFaultTerm,qmaPairDiagonal,
      qmaClockLeftTerm,qmaClockRightTerm,qmaBitDiagonal,Matrix.diagonal_apply_eq]
    change ((qmaPinnedClockPenalty c.gates.length (s ∘ Sum.inl) : ℝ) : ℂ) =
      (∑ i : Fin (c.gates.length+1), if s (Sum.inl i.castSucc) = 0 ∧
        s (Sum.inl i.succ) = 1 then (1:ℂ) else 0)+
      (if s (Sum.inl 0) = 1 then 0 else 1)+
      (if s (Sum.inl (Fin.last (c.gates.length+1))) = 0 then 0 else 1)
    unfold qmaPinnedClockPenalty qmaClockFaultCount
    rw [Complex.ofReal_add,Complex.ofReal_add,Complex.ofReal_sum]
    congr 2
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : s (Sum.inl i.castSucc) = 0 ∧ s (Sum.inl i.succ) = 1
      · simp [hi]
      · simp [hi]
    · by_cases hl : s (Sum.inl 0) = 1 <;> simp [Function.comp_apply,hl]
    · by_cases hr : s (Sum.inl (Fin.last (c.gates.length+1))) = 0
      <;> simp [Function.comp_apply,hr]
  · simp [h,Matrix.sum_apply,qmaClockFaultTerm,qmaPairDiagonal,
      qmaClockLeftTerm,qmaClockRightTerm,qmaBitDiagonal]

theorem qmaUnaryInputDiagonal_reindex (c : QMACircuit) :
    ((7:ℂ) • Matrix.diagonal (fun p => (qmaUnaryInputDiagonal c p : ℂ))).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) =
      ∑ i : Fin (c.work+1), qmaInputTerm c i := by
  rw [qmaSubmatrix_smul,Matrix.submatrix_diagonal_equiv]
  ext s r
  by_cases h : s = r
  · subst r
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,qmaInputTerm,qmaPairDiagonal,
      Matrix.diagonal_apply_eq]
    change (7:ℂ)*(if s (Sum.inl (qmaInputMarker c)) = 0 then
      (qmaAncillaCount c (s ∘ Sum.inr) : ℝ) else 0) =
      ∑ i : Fin (c.work+1), if s (Sum.inl (qmaInputMarker c)) = 0 then
        if c.witness ≤ i.val ∧ s (Sum.inr i) ≠ 0 then (7:ℂ) else 0 else 0
    by_cases hm : s (Sum.inl (qmaInputMarker c)) = 0
    · simp only [hm,ite_true,qmaAncillaCount,Complex.ofReal_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c.witness ≤ i.val ∧ s (Sum.inr i) ≠ 0
      · simp [hi]
      · simp [hi]
    · simp [hm]
  · simp [Matrix.smul_apply,h,Matrix.sum_apply,qmaInputTerm,qmaPairDiagonal]

theorem qmaUnaryOutputDiagonal_reindex (c : QMACircuit) :
    (Matrix.diagonal (fun p => (qmaUnaryOutputDiagonal c p : ℂ))).submatrix
      (qmaCircuitQubitSplit c) (qmaCircuitQubitSplit c) = qmaOutputTerm c := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext s r
  by_cases h : s = r
  · subst r
    simp only [qmaOutputTerm,qmaPairDiagonal,Matrix.diagonal_apply_eq]
    change Complex.ofReal (qmaUnaryOutputDiagonal c (qmaCircuitQubitSplit c s)) = _
    unfold qmaUnaryOutputDiagonal
    by_cases ho : s (Sum.inl (qmaOutputMarker c)) = 1 ∧ s (Sum.inr (Fin.last c.work)) ≠ 1
    · have ho' : (qmaCircuitQubitSplit c s).1 (qmaOutputMarker c) = 1 ∧
          (qmaCircuitQubitSplit c s).2 (Fin.last c.work) ≠ 1 := ho
      calc
        _ = Complex.ofReal 1 := congrArg Complex.ofReal (ite_eq_left ho')
        _ = 1 := by norm_num
        _ = _ := (ite_eq_left ho).symm
    · have ho' : ¬((qmaCircuitQubitSplit c s).1 (qmaOutputMarker c) = 1 ∧
          (qmaCircuitQubitSplit c s).2 (Fin.last c.work) ≠ 1) := ho
      calc
        _ = Complex.ofReal 0 := congrArg Complex.ofReal (ite_eq_right ho')
        _ = 0 := by norm_num
        _ = _ := (ite_eq_right ho).symm
  · simp [h,qmaOutputTerm,qmaPairDiagonal]

theorem qmaQubitHamiltonian_decomposition (c : QMACircuit) :
    qmaQubitHamiltonian c =
      ((∑ i : Fin (c.gates.length+1), qmaClockFaultTerm c i)+qmaClockLeftTerm c+qmaClockRightTerm c)+
      qmaOutputTerm c+(∑ i : Fin (c.work+1), qmaInputTerm c i)+
      (8*c.gates.length:ℂ) • ∑ t : Fin c.gates.length,
        (qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t := by
  unfold qmaQubitHamiltonian qmaUnaryHamiltonian
  simp only [qmaSubmatrix_add]
  rw [qmaUnaryClockDiagonal_reindex,qmaUnaryOutputDiagonal_reindex,
    qmaUnaryInputDiagonal_reindex,qmaSubmatrix_smul,qmaUnaryPropagationGram_reindex]

end ContinuumCoulomb

end

end OAI
