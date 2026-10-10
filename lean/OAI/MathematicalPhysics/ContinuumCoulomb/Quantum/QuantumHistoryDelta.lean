import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryComparison
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDiagonal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateEntryProgram

namespace OAI

/-! Exact register evaluation of the propagation delta.  The equality scans
are bounded by the unary circuit size; every bit is read from the supplied
local support table. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDelta
open QuantumAlgebraicScalar QuantumHistoryDescriptors QuantumHistoryBitProgram
open QuantumHistoryDiagonal QuantumHistorySiteProgram

def guard (c : QMACircuit) (t : ℕ) (d : Data) : Bool :=
  decide (clockRow c d t=1 ∧ clockRow c d (t+2)=0 ∧ clockRow c d (t+1)=0)

def flipped (c : QMACircuit) (t : ℕ) (d : Data) : Bool :=
  QuantumHistoryComparison.value
    (c.gates.length+2+(c.work+1),referenceWork c+1,true,referenceWork c+1+(t+1),d)

def sameClock (c : QMACircuit) (d : Data) : Bool :=
  QuantumHistoryComparison.value (c.gates.length+2,referenceWork c+1,false,0,d)

def entry (c : QMACircuit) (t : ℕ) (d : Data) : Scalar :=
  if guard c t d then
    sub (rat (if flipped c t d then 1 else 0))
      (mul (rat (if sameClock c d then 1 else 0))
        (QuantumGateEntryProgram.entry
          (c.work,referenceWork c+1+(c.gates.length+2),gateAt (c,t),d)))
  else rat 0

def qubitEquiv (c : QMACircuit) :
    QMACircuitQubit c ≃ Fin (c.gates.length+2+(c.work+1)) := finSumFinEquiv

theorem qubitEquiv_val (c : QMACircuit) (q : QMACircuitQubit c) :
    (qubitEquiv c q).val=distributedNumber c q := by
  cases q <;> rfl

theorem readRow_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readRow c d q=row d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (row d) (number_inr c q)

theorem readColumn_eq (c : QMACircuit) (d : Data) (q : QMACircuitQubit c) :
    readColumn c d q=column d (referenceWork c+1+(qubitEquiv c q).val) := by
  rw [qubitEquiv_val]
  exact congrArg (column d) (number_inr c q)

theorem guard_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    guard c t.val d=true ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
  have he : (clockRow c d t.val=1 ∧ clockRow c d (t.val+2)=0 ∧
      clockRow c d (t.val+1)=0) ↔
      QMAClockGuard c.gates.length t (readRow c d ∘ Sum.inl) ∧
        readRow c d (.inl (qmaClockMiddle c.gates.length t))=0 := by
    simp only [QMAClockGuard,Function.comp_apply,readRow,QuantumOrderedSupport.siteNumber,
      clockRow,referenceWork_eq,qmaClockLeft,qmaClockRight,qmaClockMiddle,and_assoc]
  exact ⟨fun h => he.mp (of_decide_eq_true h),fun h => decide_eq_true (he.mpr h)⟩

theorem flipped_iff (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    flipped c t.val d=true ↔ readRow c d=
      qmaBitFlip (.inl (qmaClockMiddle c.gates.length t)) (readColumn c d) := by
  have h := QuantumHistoryComparison.value_flip_iff (qubitEquiv c)
    (referenceWork c+1) (.inl (qmaClockMiddle c.gates.length t)) d
  have he : (qubitEquiv c (.inl (qmaClockMiddle c.gates.length t))).val=t.val+1 := rfl
  change QuantumHistoryComparison.value
    (c.gates.length+2+(c.work+1),referenceWork c+1,true,referenceWork c+1+(t.val+1),d)=true ↔ _
  simpa only [he,← readRow_eq,← readColumn_eq] using h

theorem sameClock_iff (c : QMACircuit) (d : Data) :
    sameClock c d=true ↔ readRow c d ∘ Sum.inl=readColumn c d ∘ Sum.inl := by
  have h := QuantumHistoryComparison.value_equiv_iff
    (Equiv.refl (Fin (c.gates.length+2))) (referenceWork c+1) 0 d
  simpa only [sameClock,Equiv.refl_apply,readRow,readColumn,
    QuantumOrderedSupport.siteNumber,referenceWork_eq,Function.comp_def] using h

theorem gate_entry (c : QMACircuit) (t : ℕ) (d : Data) :
    QuantumGateEntryProgram.entry
      (c.work,referenceWork c+1+(c.gates.length+2),gateAt (c,t),d)=
      QuantumAlgebraicHistory.gate c.work (gateAt (c,t))
        (readRow c d ∘ Sum.inr) (readColumn c d ∘ Sum.inr) := by
  rw [QuantumGateEntryProgram.entry_eq]
  rfl

theorem entry_actual (c : QMACircuit) (t : Fin c.gates.length) (d : Data) :
    entry c t.val d=QuantumAlgebraicHistory.delta c t (readRow c d) (readColumn c d) := by
  unfold entry QuantumAlgebraicHistory.delta QuantumAlgebraicHistory.identity
  rw [gate_entry]
  simp only [flipped_iff c t d,sameClock_iff c d,gateAt]
  by_cases hg : guard c t.val d=true
  · have hh := (guard_iff c t d).mp hg
    simp only [hg,hh,and_self,ite_true]
  · have hh := mt (guard_iff c t d).mpr hg
    simp only [hg,hh,Bool.false_eq_true,ite_false]

end ContinuumCoulomb.QuantumHistoryDelta

end

end OAI
