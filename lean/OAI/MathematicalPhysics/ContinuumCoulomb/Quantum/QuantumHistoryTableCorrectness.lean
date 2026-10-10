import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryTableProgram

namespace OAI

/-! The total table dispatcher agrees with the actual ordered history core,
including its canonical finite enumeration. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryTableProgram
open QuantumHistoryDescriptors QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical

theorem nondiagonal_term (c : QMACircuit) (a : QMACircuitTerm c)
    (ha : ¬(encode c a).1<4) :
    ∃ t : Fin c.gates.length, a=QuantumPropagationOrder.term c t := by
  rcases a with i | (b | (i | (u | t)))
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · norm_num [encode] at ha
  · exact ⟨t,rfl⟩

theorem propagationLabels_tail (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    (QuantumOrderedSupport.encodedSites c hT (.inl i)).tail=
      QuantumPropagationSupport.labels c t := by
  simp only [QuantumOrderedSupport.encodedSites,QuantumPropagationOrder.sites_eq c hT i t ht,
    List.map_cons,List.tail_cons,List.map_map,Function.comp_def,QuantumPropagationSupport.labels]

theorem localTable_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    localTable (QuantumOrderedSupport.sites c hT a).length
      (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  cases a with
  | inl i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,i.val,QuantumOrderedSupport.encodedSites c hT (.inl i))=_
    have hi : i.val<referenceWork c+1 := i.isLt
    simp only [localTable,hi,ite_true,orderedAt_actual c hT i]
    by_cases ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4
    · rw [ite_eq_left ha]
      exact QuantumHistoryDiagonal.tableList_actual c hT i ha
    · rw [ite_eq_right ha]
      obtain ⟨t,ht⟩ := nondiagonal_term c
        (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) ha
      rw [ht,propagationLabels_tail c hT i t ht]
      exact QuantumPropagationSampler.tableList_actual c hT i t ht
  | inr i =>
    change localTable (QuantumOrderedSupport.sites c hT (.inr i)).length
      (c,qmaHistoryReferenceWork c+1+i.val,QuantumOrderedSupport.encodedSites c hT (.inr i))=_
    have hi : ¬qmaHistoryReferenceWork c+1+i.val<qmaHistoryReferenceWork c+1 := by
      omega
    simp only [localTable,referenceWork_eq,hi,ite_false,Nat.add_sub_cancel_left]
    exact congrArg matrixData (QuantumReferenceEdgeTable.table_actual c hT i)

theorem table_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    table (c,((QuantumOrderedSourceIndex.reference c).symm a).val,
        QuantumOrderedSupport.encodedSites c hT a)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT a) := by
  rw [table_eq _ (by
    simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using
      QuantumOrderedSupport.sites_length c hT a)]
  simpa only [QuantumOrderedSupport.encodedSites,List.length_map] using localTable_actual c hT a

end ContinuumCoulomb.QuantumHistoryTableProgram

end

end OAI
