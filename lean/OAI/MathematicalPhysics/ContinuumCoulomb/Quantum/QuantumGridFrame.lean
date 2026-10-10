import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMappedGate

namespace OAI

/-! The cumulative row-transfer frame locates the active register exactly. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaGridFrame (rows width : ℕ) : (t : ℕ) → t ≤ rows →
    Equiv.Perm (Fin (qmaGridWork rows width+1))
  | 0,_ => Equiv.refl _
  | t+1,ht =>
      (qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width (⟨t,by omega⟩ : Fin (rows+1)))
        (qmaGridQubit rows width (⟨t+1,by omega⟩ : Fin (rows+1))))).trans
          (qmaGridFrame rows width t (by omega))

theorem qmaGridFrame_active (rows width t : ℕ) (ht : t ≤ rows) (i : Fin (width+1)) :
    (qmaGridFrame rows width t ht).symm (qmaGridQubit rows width 0 i) =
      qmaGridQubit rows width ⟨t,by omega⟩ i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hp : t ≤ rows := by omega
    let r : Fin rows := ⟨t,by omega⟩
    change (qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ))).symm
        ((qmaGridFrame rows width t hp).symm (qmaGridQubit rows width 0 i)) = _
    rw [ih hp]
    exact (qmaTransferPermutation (qmaRowPairs (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ))).symm_apply_eq.mpr
        (qmaGridTransfer_coordinates rows width r i).2.symm

theorem qmaGridFrame_gate (rows width t : ℕ) (ht : t ≤ rows) (g : QMAGate) :
    qmaRelabelGate (qmaGridWork rows width) (qmaGridFrame rows width t ht).symm
      (qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width 0) g) =
    qmaMapGate width (qmaGridWork rows width) (qmaGridQubit rows width ⟨t,by omega⟩) g := by
  rw [qmaRelabelGate_map]
  apply qmaMapGate_congr
  intro i
  exact qmaGridFrame_active rows width t ht i

end ContinuumCoulomb

end

end OAI
