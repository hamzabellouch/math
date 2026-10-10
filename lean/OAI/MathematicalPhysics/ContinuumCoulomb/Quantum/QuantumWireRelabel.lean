import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateProduct

namespace OAI

/-! Exact coordinate changes for gates and circuit products. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaWireBasis {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    SourceSpinBasis n ≃ SourceSpinBasis n where
  toFun s := s ∘ σ
  invFun s := s ∘ σ.symm
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

def qmaWireRelabelMatrix {n : ℕ} (σ : Equiv.Perm (Fin n))
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :=
  M.submatrix (qmaWireBasis σ) (qmaWireBasis σ)

theorem sourceTensor_wire_relabel {n : ℕ} (σ : Equiv.Perm (Fin n))
    (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    sourceTensor n (fun k => M (σ.symm k)) = qmaWireRelabelMatrix σ (sourceTensor n M) := by
  ext s t
  change (∏ k, M (σ.symm k) (s k) (t k)) = ∏ k, M k (s (σ k)) (t (σ k))
  exact Fintype.prod_equiv σ.symm _ _ (by intro k; simp)

def qmaRelabelGate (work : ℕ) (σ : Equiv.Perm (Fin (work+1))) : QMAGate → QMAGate
  | .hadamard i => .hadamard (σ (qmaQubit work i)).val
  | .phaseT i => .phaseT (σ (qmaQubit work i)).val
  | .controlledNot i j =>
      .controlledNot (σ (qmaQubit work i)).val (σ (qmaQubit work j)).val

theorem qmaControlledNot_wire_relabel (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (i j : Fin (work+1)) (s : SourceSpinBasis (work+1)) :
    qmaControlledNot work i j (qmaWireBasis σ s) =
      qmaWireBasis σ (qmaControlledNot work (σ i) (σ j) s) := by
  funext k
  by_cases hk : k = j
  · subst k
    by_cases hs : s (σ i) = 1 <;> simp [qmaControlledNot,qmaWireBasis,hs]
  · have hσ : σ k ≠ σ j := fun h => hk (σ.injective h)
    simp [qmaControlledNot,qmaWireBasis,hk,hσ]

theorem qmaRelabelGate_matrix (work : ℕ) (σ : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    qmaGateMatrix work (qmaRelabelGate work σ g) =
      qmaWireRelabelMatrix σ (qmaGateMatrix work g) := by
  cases g with
  | hadamard i =>
    simp only [qmaRelabelGate,qmaGateMatrix,qmaQubit_fin]
    rw [← sourceTensor_wire_relabel]
    congr 1
    funext k
    simp [Equiv.symm_apply_eq]
  | phaseT i =>
    simp only [qmaRelabelGate,qmaGateMatrix,qmaQubit_fin]
    rw [← sourceTensor_wire_relabel]
    congr 1
    funext k
    simp [Equiv.symm_apply_eq]
  | controlledNot i j =>
    simp only [qmaRelabelGate,qmaGateMatrix,qmaQubit_fin]
    ext s t
    change (if s = qmaControlledNot work (σ (qmaQubit work i)) (σ (qmaQubit work j)) t
      then (1:ℂ) else 0) =
      if qmaWireBasis σ s = qmaControlledNot work (qmaQubit work i) (qmaQubit work j)
        (qmaWireBasis σ t) then 1 else 0
    simp only [qmaControlledNot_wire_relabel, (qmaWireBasis σ).injective.eq_iff]

theorem qmaRelabelGate_wellFormed (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) (hg : g.WellFormed (work+1)) :
    (qmaRelabelGate work σ g).WellFormed (work+1) := by
  cases g with
  | hadamard i => exact (σ (qmaQubit work i)).isLt
  | phaseT i => exact (σ (qmaQubit work i)).isLt
  | controlledNot i j =>
    refine ⟨(σ (qmaQubit work i)).isLt,(σ (qmaQubit work j)).isLt,?_⟩
    intro h
    have he := σ.injective (Fin.ext h)
    have hv := congrArg Fin.val he
    simp only [qmaQubit,Nat.mod_eq_of_lt hg.1,Nat.mod_eq_of_lt hg.2.1] at hv
    exact hg.2.2 hv

theorem qmaWireRelabelMatrix_mul {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A B : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    qmaWireRelabelMatrix σ (A*B) = qmaWireRelabelMatrix σ A*qmaWireRelabelMatrix σ B := by
  exact (Matrix.submatrix_mul_equiv A B (qmaWireBasis σ) (qmaWireBasis σ)
    (qmaWireBasis σ)).symm

theorem qmaGateProduct_relabel (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (gs : List QMAGate) :
    qmaGateProduct work (gs.map (qmaRelabelGate work σ)) =
      qmaWireRelabelMatrix σ (qmaGateProduct work gs) := by
  induction gs using List.reverseRecOn with
  | nil => simp [qmaGateProduct_nil,qmaWireRelabelMatrix,Matrix.submatrix_one_equiv]
  | append_singleton gs g ih =>
    simp only [List.map_append,List.map_cons,List.map_nil,qmaGateProduct_append,
      qmaGateProduct_singleton,qmaWireRelabelMatrix_mul,qmaRelabelGate_matrix,ih]

end ContinuumCoulomb

end

end OAI
