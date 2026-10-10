import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedBasis

namespace OAI

/-! Fresh wires are exact identity spectators for the lifted verifier circuit. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaControlledNot_padded_left (work extra : ℕ) (c t : Fin (work+1))
    (s : SourceSpinBasis (work+extra+1)) :
    (qmaPaddedBasis work extra
      (qmaControlledNot (work+extra) (qmaPaddedLeft work extra c) (qmaPaddedLeft work extra t) s)).1 =
    qmaControlledNot work c t (qmaPaddedBasis work extra s).1 := by
  funext i
  by_cases hit : i = t
  · subst i
    by_cases hc : s (qmaPaddedLeft work extra c) = 1 <;>
      simp [qmaControlledNot,qmaPaddedBasis_left,hc]
  · have hleft := (qmaPaddedLeft_injective work extra).ne hit
    simp [qmaPaddedBasis_left,qmaControlledNot,hit,hleft]

theorem qmaControlledNot_padded_right (work extra : ℕ) (c t : Fin (work+1))
    (s : SourceSpinBasis (work+extra+1)) :
    (qmaPaddedBasis work extra
      (qmaControlledNot (work+extra) (qmaPaddedLeft work extra c) (qmaPaddedLeft work extra t) s)).2 =
    (qmaPaddedBasis work extra s).2 := by
  funext j
  have hj := (qmaPaddedLeft_ne_right work extra t j).symm
  simp [qmaPaddedBasis_right,qmaControlledNot,hj]

theorem qmaGateMatrix_padded (work extra : ℕ) (g : QMAGate) :
    (qmaGateMatrix (work+extra) (qmaMapGate work (work+extra) (qmaPaddedLeft work extra) g)).submatrix
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
      qmaGateMatrix work g ⊗ₖ (1 : Matrix (SourceSpinBasis extra) (SourceSpinBasis extra) ℂ) := by
  cases g with
  | hadamard i =>
    simp only [qmaMapGate,qmaGateMatrix,qmaQubit_fin]
    rw [sourceTensor_padded]
    have hl : (fun k : Fin (work+1) =>
        if qmaPaddedLeft work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaHadamard else 1) = (fun k => if k = qmaQubit work i then qmaHadamard else 1) := by
      funext k
      simp only [(qmaPaddedLeft_injective work extra).eq_iff]
    have hr : (fun k : Fin extra =>
        if qmaPaddedRight work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaHadamard else 1) = (fun _ => 1) := by
      funext k
      exact ite_eq_right (qmaPaddedLeft_ne_right work extra (qmaQubit work i) k).symm
    rw [hl,hr,sourceTensor_one]
  | phaseT i =>
    simp only [qmaMapGate,qmaGateMatrix,qmaQubit_fin]
    rw [sourceTensor_padded]
    have hl : (fun k : Fin (work+1) =>
        if qmaPaddedLeft work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaPhaseT else 1) = (fun k => if k = qmaQubit work i then qmaPhaseT else 1) := by
      funext k
      simp only [(qmaPaddedLeft_injective work extra).eq_iff]
    have hr : (fun k : Fin extra =>
        if qmaPaddedRight work extra k = qmaPaddedLeft work extra (qmaQubit work i)
        then qmaPhaseT else 1) = (fun _ => 1) := by
      funext k
      exact ite_eq_right (qmaPaddedLeft_ne_right work extra (qmaQubit work i) k).symm
    rw [hl,hr,sourceTensor_one]
  | controlledNot i j =>
    simp only [qmaMapGate,qmaGateMatrix,qmaQubit_fin]
    ext p q
    let B := qmaPaddedBasis work extra
    let F := qmaControlledNot (work+extra) (qmaPaddedLeft work extra (qmaQubit work i))
      (qmaPaddedLeft work extra (qmaQubit work j))
    let f := qmaControlledNot work (qmaQubit work i) (qmaQubit work j)
    have hb : B (F (B.symm q)) = (f q.1,q.2) := by
      apply Prod.ext
      · rw [qmaControlledNot_padded_left]
        simp only [B,f,Equiv.apply_symm_apply]
      · rw [qmaControlledNot_padded_right]
        simp only [B,Equiv.apply_symm_apply]
    have he : B.symm p = F (B.symm q) ↔ p = (f q.1,q.2) := by
      constructor
      · intro h
        simpa only [Equiv.apply_symm_apply,hb] using congrArg B h
      · intro h
        apply B.injective
        simpa only [Equiv.apply_symm_apply,hb] using h
    change (if B.symm p = F (B.symm q) then (1:ℂ) else 0) =
      (if p.1 = f q.1 then 1 else 0)*(if p.2 = q.2 then 1 else 0)
    by_cases h₁ : p.1 = f q.1 <;> by_cases h₂ : p.2 = q.2 <;>
      simp [he,Prod.ext_iff,h₁,h₂]

theorem qmaGateProduct_padded (work extra : ℕ) (gs : List QMAGate) :
    (qmaGateProduct (work+extra) (gs.map (qmaMapGate work (work+extra) (qmaPaddedLeft work extra)))).submatrix
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
      qmaGateProduct work gs ⊗ₖ (1 : Matrix (SourceSpinBasis extra) (SourceSpinBasis extra) ℂ) := by
  induction gs using List.reverseRecOn with
  | nil => simp [qmaGateProduct_nil,Matrix.submatrix_one_equiv]
  | append_singleton gs g ih =>
    simp only [List.map_append,List.map_cons,List.map_nil,qmaGateProduct_append,
      qmaGateProduct_singleton]
    rw [←Matrix.submatrix_mul_equiv _ _ (qmaPaddedBasis work extra).symm
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm,
      qmaGateMatrix_padded,ih,←Matrix.mul_kronecker_mul,one_mul]

end ContinuumCoulomb

end

end OAI
