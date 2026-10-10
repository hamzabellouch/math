import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDescriptorSites
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryBitProgram

namespace OAI

/-! The four diagonal descriptor cases are evaluated directly from their
clock/work bits.  Their values are exact rational entries of the actual
distributed history operator, before the rebit construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open QuantumHistoryDescriptors QuantumHistorySiteProgram QuantumHistoryBitProgram
open QuantumAlgebraicScalar
open scoped Classical

def clockRow (c : QMACircuit) (d : Data) (i : ℕ) : Fin 2 :=
  row d (referenceWork c+1+i)

def workRow (c : QMACircuit) (d : Data) (i : ℕ) : Fin 2 :=
  row d (referenceWork c+1+(c.gates.length+2)+i)

def readRow (c : QMACircuit) (d : Data) : QMACircuitQubit c → Fin 2 :=
  fun q => row d (QuantumOrderedSupport.siteNumber c (.inr q))

def readColumn (c : QMACircuit) (d : Data) : QMACircuitQubit c → Fin 2 :=
  fun q => column d (QuantumOrderedSupport.siteNumber c (.inr q))

def weight (c : QMACircuit) (a : Descriptor) (d : Data) : ℚ :=
  if a.1=0 then
    (if clockRow c d a.2=0 ∧ clockRow c d (a.2+1)=1 then 1 else 0) else
  if a.1=1 then
    (if a.2=0 then (if clockRow c d 0=1 then 0 else 1)
      else (if clockRow c d (c.gates.length+1)=0 then 0 else 1)) else
  if a.1=2 then
    let time := QuantumFirstUseProgram.value (c,a.2)
    if clockRow c d time=1 ∧ clockRow c d (time+1)=0 ∧
        c.witness ≤ a.2 ∧ workRow c d a.2≠0 then 14 else 0 else
  if a.1=3 then
    (if clockRow c d c.gates.length=1 ∧ workRow c d c.work≠1 then 1 else 0) else 0

theorem distributed_entry (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : (encode c a).1<4) (d : Data) :
    QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c) a
      (readRow c d) (readColumn c d) =
    if readRow c d=readColumn c d then rat (weight c (encode c a) d) else rat 0 := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;> rfl
  · change (if readRow c d=readColumn c d then rat
        (if qmaClockAt c.gates.length (qmaFirstUseTime c i) (readRow c d ∘ Sum.inl) ∧
          qmaInputCheck c i (readRow c d ∘ Sum.inr) then 14 else 0) else rat 0) =
      if readRow c d=readColumn c d then rat
        (if clockRow c d (QuantumFirstUseProgram.value (c,i.val))=1 ∧
          clockRow c d (QuantumFirstUseProgram.value (c,i.val)+1)=0 ∧
          c.witness ≤ i.val ∧ workRow c d i.val≠0 then 14 else 0) else rat 0
    simp only [QuantumFirstUseProgram.value_eq]
    unfold qmaClockAt qmaInputCheck
    have he : (clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0) ∧
        (c.witness ≤ i.val ∧ workRow c d i.val≠0) ↔
      clockRow c d (qmaFirstUse c i)=1 ∧
        clockRow c d (qmaFirstUse c i+1)=0 ∧
        c.witness ≤ i.val ∧ workRow c d i.val≠0 := by tauto
    simp only [readRow,clockRow,workRow,referenceWork_eq,
      QuantumOrderedSupport.siteNumber,Function.comp_apply,Fin.val_castSucc,Fin.val_succ] at *
    simp only [he]
    rfl
  · cases u
    rfl
  · norm_num [encode] at ha

def supportData (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) : Data :=
  (QuantumOrderedSupport.encodedSites c hT a,
    QuantumSupportLookup.supportBits c hT a s,QuantumSupportLookup.supportBits c hT a t)

theorem readRow_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readRow c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => s ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.row_actual c hT a s t (.inr q)

theorem readColumn_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) :
    readColumn c (supportData c hT a s t) = fun q =>
      qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => t ((QuantumOrderedSupport.supportEquiv c hT a).symm j)) (.inr q) := by
  funext q
  exact QuantumHistoryBitProgram.column_actual c hT a s t (.inr q)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
