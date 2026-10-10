import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridCircuit

namespace OAI

/-! Splitting the original register from fresh grid wires. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaAppendBasis (n m : ℕ) : SourceSpinBasis (n+m) ≃ SourceSpinBasis n × SourceSpinBasis m where
  toFun s := (fun i => s (Fin.castAdd m i),fun j => s (Fin.natAdd n j))
  invFun p := Fin.addCases p.1 p.2
  left_inv s := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.addCases_left]
    · simp only [Fin.addCases_right]
  right_inv p := by simp

def qmaPaddedIndex (work extra : ℕ) : Fin ((work+1)+extra) ≃ Fin (work+extra+1) :=
  finCongr (by omega)

def qmaPaddedBasis (work extra : ℕ) :
    SourceSpinBasis (work+extra+1) ≃ SourceSpinBasis (work+1) × SourceSpinBasis extra :=
  (Equiv.arrowCongr (qmaPaddedIndex work extra).symm (Equiv.refl (Fin 2))).trans
    (qmaAppendBasis (work+1) extra)

def qmaPaddedLeft (work extra : ℕ) (i : Fin (work+1)) : Fin (work+extra+1) :=
  qmaPaddedIndex work extra (Fin.castAdd extra i)

def qmaPaddedRight (work extra : ℕ) (i : Fin extra) : Fin (work+extra+1) :=
  qmaPaddedIndex work extra (Fin.natAdd (work+1) i)

theorem qmaPaddedLeft_injective (work extra : ℕ) : Function.Injective (qmaPaddedLeft work extra) :=
  (qmaPaddedIndex work extra).injective.comp (Fin.castAdd_injective (work+1) extra)

theorem qmaPaddedLeft_ne_right (work extra : ℕ) (i : Fin (work+1)) (j : Fin extra) :
    qmaPaddedLeft work extra i ≠ qmaPaddedRight work extra j := by
  intro h
  have hv := congrArg Fin.val ((qmaPaddedIndex work extra).injective h)
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

theorem qmaPaddedBasis_left (work extra : ℕ) (s : SourceSpinBasis (work+extra+1))
    (i : Fin (work+1)) : (qmaPaddedBasis work extra s).1 i = s (qmaPaddedLeft work extra i) := rfl

theorem qmaPaddedBasis_right (work extra : ℕ) (s : SourceSpinBasis (work+extra+1))
    (i : Fin extra) : (qmaPaddedBasis work extra s).2 i = s (qmaPaddedRight work extra i) := rfl

theorem qmaPaddedBasis_symm_left (work extra : ℕ)
    (p : SourceSpinBasis (work+1) × SourceSpinBasis extra) (i : Fin (work+1)) :
    (qmaPaddedBasis work extra).symm p (qmaPaddedLeft work extra i) = p.1 i :=
  congrFun (congrArg Prod.fst ((qmaPaddedBasis work extra).apply_symm_apply p)) i

theorem qmaPaddedBasis_symm_right (work extra : ℕ)
    (p : SourceSpinBasis (work+1) × SourceSpinBasis extra) (i : Fin extra) :
    (qmaPaddedBasis work extra).symm p (qmaPaddedRight work extra i) = p.2 i :=
  congrFun (congrArg Prod.snd ((qmaPaddedBasis work extra).apply_symm_apply p)) i

theorem sourceTensor_padded (work extra : ℕ)
    (M : Fin (work+extra+1) → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor (work+extra+1) M).submatrix
      (qmaPaddedBasis work extra).symm (qmaPaddedBasis work extra).symm =
    sourceTensor (work+1) (fun i => M (qmaPaddedLeft work extra i)) ⊗ₖ
      sourceTensor extra (fun j => M (qmaPaddedRight work extra j)) := by
  ext p q
  change (∏ k, M k ((qmaPaddedBasis work extra).symm p k)
    ((qmaPaddedBasis work extra).symm q k)) = _
  rw [← (qmaPaddedIndex work extra).prod_comp]
  rw [Fin.prod_univ_add]
  change (∏ i, M (qmaPaddedLeft work extra i)
    ((qmaPaddedBasis work extra).symm p (qmaPaddedLeft work extra i))
    ((qmaPaddedBasis work extra).symm q (qmaPaddedLeft work extra i)))*
    (∏ j, M (qmaPaddedRight work extra j)
    ((qmaPaddedBasis work extra).symm p (qmaPaddedRight work extra j))
    ((qmaPaddedBasis work extra).symm q (qmaPaddedRight work extra j))) = _
  simp only [qmaPaddedBasis_symm_left,qmaPaddedBasis_symm_right]
  rfl

end ContinuumCoulomb

end

end OAI
