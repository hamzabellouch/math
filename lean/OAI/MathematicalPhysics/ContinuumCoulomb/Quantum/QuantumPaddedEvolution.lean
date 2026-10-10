import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedInput

namespace OAI

/-! Exact tensor evolution of the verifier together with zero fresh wires. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaTensor_zero_vector {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α α ℂ) (u : α → ℂ) (b : β) (p : α × β) :
    (M ⊗ₖ (1 : Matrix β β ℂ)).mulVec (fun q => u q.1*(if q.2 = b then 1 else 0)) p =
      M.mulVec u p.1*(if p.2 = b then 1 else 0) := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  by_cases hp : p.2 = b <;> simp [Matrix.one_apply,hp]

theorem qmaPadded_apply (work extra : ℕ)
    (N : Matrix (SourceSpinBasis (work+extra+1)) (SourceSpinBasis (work+extra+1)) ℂ)
    (M : Matrix (SourceSpinBasis (work+1)) (SourceSpinBasis (work+1)) ℂ)
    (hN : N.submatrix (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
      M ⊗ₖ (1 : Matrix (SourceSpinBasis extra) (SourceSpinBasis extra) ℂ))
    (v : SourceSpinBasis (work+extra+1) → ℂ) (u : SourceSpinBasis (work+1) → ℂ)
    (hv : ∀ s, v s = u (qmaPaddedBasis work extra s).1*
      (if (qmaPaddedBasis work extra s).2 = 0 then 1 else 0))
    (s : SourceSpinBasis (work+extra+1)) :
    N.mulVec v s = M.mulVec u (qmaPaddedBasis work extra s).1*
      (if (qmaPaddedBasis work extra s).2 = 0 then 1 else 0) := by
  let B := qmaPaddedBasis work extra
  have hu : v ∘ B.symm = fun p => u p.1*(if p.2 = 0 then 1 else 0) := by
    funext p
    simp only [Function.comp_apply,hv,B,Equiv.apply_symm_apply]
  have h := Matrix.submatrix_mulVec_equiv N (v ∘ B.symm) B.symm B.symm
  have he : (v ∘ B.symm) ∘ B = v := by funext s; simp
  change N.submatrix B.symm B.symm *ᵥ (v ∘ B.symm) =
    (N *ᵥ ((v ∘ B.symm) ∘ B)) ∘ B.symm at h
  rw [he,show N.submatrix B.symm B.symm = _ from hN,hu] at h
  have hp := congrFun h (B s)
  simpa only [Function.comp_apply,Equiv.symm_apply_apply,qmaTensor_zero_vector] using hp.symm

theorem qmaOutputVector_padded (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness))
    (s : SourceSpinBasis (c.work+extra+1)) :
    qmaOutputVector (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi s =
      qmaOutputVector c hc psi (qmaPaddedBasis c.work extra s).1 *
        if (qmaPaddedBasis c.work extra s).2 = 0 then 1 else 0 := by
  apply qmaPadded_apply c.work extra (qmaCircuitMatrix (qmaPaddedCircuit c extra))
    (qmaCircuitMatrix c) (qmaGateProduct_padded c.work extra c.gates)
    (qmaInitialState (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi)
    (qmaInitialState c hc psi) (qmaInitialState_padded c hc extra psi) s

theorem qmaPaddedOutput_probability (c : QMACircuit) (hc : c.WellFormed) (extra : ℕ)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (i : Fin (c.work+1)) (b : Fin 2) :
    ‖qmaMask (fun s => s (qmaPaddedLeft c.work extra i) = b)
      (qmaOutputVector (qmaPaddedCircuit c extra) (qmaPaddedCircuit_wellFormed c hc extra) psi)‖^2 =
    ‖qmaMask (fun s => s i = b) (qmaOutputVector c hc psi)‖^2 := by
  have hout (p : SourceSpinBasis (c.work+1) × SourceSpinBasis extra) :
      (qmaOutputVector (qmaPaddedCircuit c extra)
        (qmaPaddedCircuit_wellFormed c hc extra) psi).ofLp
          ((qmaPaddedBasis c.work extra).symm p) =
      (qmaOutputVector c hc psi).ofLp p.1 * (if p.2 = 0 then 1 else 0) := by
    simpa only [Equiv.apply_symm_apply] using
      qmaOutputVector_padded c hc extra psi ((qmaPaddedBasis c.work extra).symm p)
  rw [qmaMask_norm_sq,qmaMask_norm_sq]
  rw [←(qmaPaddedBasis c.work extra).symm.sum_comp]
  simp only [hout,qmaPaddedBasis_symm_left,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a i = b
  · simp only [ha,ite_true]
    rw [Finset.sum_eq_single (0 : SourceSpinBasis extra)]
    · simp
    · intro x _ hx
      simp [hx]
    · simp
  · simp [ha]

end ContinuumCoulomb

end

end OAI
