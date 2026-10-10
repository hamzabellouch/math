import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepEndpoint
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridCoordinates

namespace OAI

/-! The last physical gate sits immediately above the output qubit. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaSparseTags_last (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length) :
    (qmaSparseTags c).getLast?.map Prod.snd = some
      ((⟨(qmaNearestCircuit c).gates.length-1,by omega⟩ :
        Fin ((qmaNearestCircuit c).gates.length+1)),Fin.last c.work) := by
  have hn : (qmaNearestCircuit c).gates ≠ [] := by
    intro he
    have hl := qmaSweepCircuitFrom_length (qmaNearestCircuit c).gates.length c.work 0
      (qmaNearestCircuit c).gates (by omega)
    change (qmaSparseCircuit c).gates.length = _ at hl
    rw [hl,he] at hT
    simp at hT
  have hl := qmaTaggedSweepFrom_last_nonempty (qmaNearestCircuit c).gates.length c.work 0
    (qmaNearestCircuit c).gates (by omega) hn
  simpa only [qmaSparseTags,Nat.zero_add,Nat.sub_zero,Nat.sub_self,qmaSweepOrder,
    Nat.zero_mod,ite_true,Equiv.refl_apply] using hl

theorem qmaSparseGateCell_last (c : QMACircuit)
    (hT : 0 < (qmaSparseCircuit c).gates.length) :
    qmaSparseGateCell c ⟨(qmaSparseCircuit c).gates.length-1,by omega⟩ =
      ((⟨(qmaNearestCircuit c).gates.length-1,by omega⟩ :
        Fin ((qmaNearestCircuit c).gates.length+1)),Fin.last c.work) := by
  have hl := qmaSparseTags_last c hT
  have hlen := qmaSparseTags_length c
  have hb : (qmaSparseTags c).length-1 < (qmaSparseTags c).length := by omega
  rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem hb] at hl
  simp only [Option.map_some,Option.some.injEq] at hl
  unfold qmaSparseGateCell qmaSparseCell
  simpa only [Fin.val_cast,hlen] using hl

theorem qmaGridQubit_last (rows width : ℕ) :
    qmaGridQubit rows width (Fin.last rows) (Fin.last width) =
      Fin.last (qmaGridWork rows width) := by
  apply Fin.ext
  simp only [qmaGridQubit,Fin.val_last,qmaGridWork]
  omega

theorem qmaSparseWorkCell_last (c : QMACircuit) :
    qmaSparseWorkCell c (Fin.last (qmaSparseCircuit c).work) =
      (Fin.last (qmaNearestCircuit c).gates.length,Fin.last c.work) := by
  change qmaGridCoordinates (qmaNearestCircuit c).gates.length c.work
    (Fin.last (qmaGridWork (qmaNearestCircuit c).gates.length c.work)) = _
  rw [←qmaGridQubit_last,qmaGridCoordinates_left]

end ContinuumCoulomb

end

end OAI
