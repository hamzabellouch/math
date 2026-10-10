import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalPropagation

namespace OAI

/-! Exact agreement of the local propagation operator with the full
unary-clock Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaLocalPropagationDelta_action (c : QMACircuit) (t : Fin c.gates.length)
    (u : QMAUnaryBasis c → ℂ) (s : QMACircuitQubit c → Fin 2) :
    (qmaLocalPropagationDelta c t).mulVec (u ∘ qmaCircuitQubitSplit c) s =
      qmaUnaryPropagationMap c u (t,qmaCircuitQubitSplit c s) := by
  rw [qmaLocalPropagationDelta,←Matrix.mulVec_mulVec,qmaGuardProjection,Matrix.mulVec_diagonal]
  by_cases h : QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
      s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0
  · rw [ite_eq_left h,one_mul,Matrix.sub_mulVec]
    change (qmaBitFlipMatrix (Sum.inl (qmaClockMiddle c.gates.length t))).mulVec
      (u ∘ qmaCircuitQubitSplit c) s-
      (qmaJoinMatrix 1 (qmaStepMatrix c t.val)).mulVec (u ∘ qmaCircuitQubitSplit c) s = _
    rw [qmaBitFlipMatrix_mulVec,qmaJoinMatrix_one_left_mulVec]
    have he : qmaCircuitQubitSplit c (qmaBitFlip (Sum.inl (qmaClockMiddle c.gates.length t)) s) =
        (Function.update (s ∘ Sum.inl) (qmaClockMiddle c.gates.length t) 1,s ∘ Sum.inr) := by
      apply Prod.ext
      · funext i
        by_cases hi : i = qmaClockMiddle c.gates.length t
        · subst i
          simp [qmaCircuitQubitSplit,qmaBitFlip,h.2]
        · simp [qmaCircuitQubitSplit,qmaBitFlip,hi]
      · funext i
        simp [qmaCircuitQubitSplit,qmaBitFlip]
    change u (qmaCircuitQubitSplit c (qmaBitFlip _ s))-
      (qmaStepMatrix c t.val).mulVec
        (fun b => u (qmaCircuitQubitSplit c (Sum.elim (s ∘ Sum.inl) b))) (s ∘ Sum.inr) = _
    rw [he]
    change _ = if QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
        s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0 then _ else _
    rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h,zero_mul]
    exact (ite_eq_right h).symm

def qmaPropagationSlice (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMAUnaryBasis c) (QMAUnaryBasis c) ℂ :=
  (qmaUnaryPropagationMatrix c).submatrix (fun p => (t,p)) id

theorem qmaPropagationSlice_eq (c : QMACircuit) (t : Fin c.gates.length) :
    qmaPropagationSlice c t = (qmaLocalPropagationDelta c t).submatrix
      (qmaCircuitQubitSplit c).symm (qmaCircuitQubitSplit c).symm := by
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  funext p
  have h := qmaLocalPropagationDelta_action c t u ((qmaCircuitQubitSplit c).symm p)
  rw [Matrix.submatrix_mulVec_equiv]
  have he : u ∘ ((qmaCircuitQubitSplit c).symm).symm = u ∘ qmaCircuitQubitSplit c := rfl
  rw [he]
  change ((qmaUnaryPropagationMatrix c).mulVec u) (t,p) = _
  rw [qmaUnaryPropagationMatrix,LinearMap.toMatrix'_mulVec]
  simpa only [Equiv.apply_symm_apply,Function.comp_apply] using h.symm

theorem qmaUnaryPropagationGram_sum (c : QMACircuit) :
    (qmaUnaryPropagationMatrix c).conjTranspose*qmaUnaryPropagationMatrix c =
      ∑ t : Fin c.gates.length, (qmaPropagationSlice c t).conjTranspose*qmaPropagationSlice c t := by
  ext p q
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type,qmaPropagationSlice,Matrix.submatrix_apply,id_eq]

end ContinuumCoulomb

end

end OAI
