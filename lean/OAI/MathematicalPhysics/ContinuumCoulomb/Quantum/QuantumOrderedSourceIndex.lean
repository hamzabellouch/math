import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelTable
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedHistory

namespace OAI

/-! Explicit finite sum/product indices for the history qubits and padded
terms. Their natural values are the literal support-list site numbers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSourceIndex
open scoped Classical

def qubitCount (c : QMACircuit) : ℕ :=
  qmaHistoryReferenceWork c+1+((c.gates.length+2)+(c.work+1))

def qubits (c : QMACircuit) : Fin (qubitCount c) ≃ QuantumOrderedSupport.Qubit c :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.symm))

theorem qubitCount_eq (c : QMACircuit) : qubitCount c=3*c.gates.length+2*c.work+8 := by
  simp only [qubitCount,qmaHistoryReferenceWork]
  omega

theorem qubits_index (c : QMACircuit) :
    QuantumOrderedLabelTable.index (qubits c)=QuantumOrderedSupport.siteNumber c := by
  funext i
  rcases i with i | (i | i)
  · rfl
  · rfl
  · change qmaHistoryReferenceWork c+1+((c.gates.length+2)+i.val) =
      qmaHistoryReferenceWork c+1+(c.gates.length+2)+i.val
    omega

def referenceCount (c : QMACircuit) : ℕ :=
  (qmaHistoryReferenceWork c+1)+qmaHistoryReferenceWork c

def reference (c : QMACircuit) :
    Fin (referenceCount c) ≃ QMAReferenceTerm (qmaHistoryReferenceWork c) :=
  finSumFinEquiv.symm

theorem referenceCount_eq (c : QMACircuit) :
    referenceCount c=4*c.gates.length+2*c.work+9 := by
  simp only [referenceCount,qmaHistoryReferenceWork]
  omega

abbrev Pattern := Fin 6 → Fin 4
def patternCount : ℕ := Fintype.card Pattern
noncomputable def patterns : Fin patternCount ≃ Pattern := (Fintype.equivFin Pattern).symm

def termCount (c : QMACircuit) : ℕ := referenceCount c*patternCount
noncomputable def terms (c : QMACircuit) : Fin (termCount c) ≃ QuantumPaddedHistory.Term c :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (reference c) patterns)

theorem termCount_eq (c : QMACircuit) :
    termCount c=4096*(4*c.gates.length+2*c.work+9) := by
  rw [termCount,referenceCount_eq]
  have h : patternCount=4096 := by
    norm_num [patternCount,Pattern,Fintype.card_fun]
  rw [h,Nat.mul_comm]

end ContinuumCoulomb.QuantumOrderedSourceIndex

end

end OAI
