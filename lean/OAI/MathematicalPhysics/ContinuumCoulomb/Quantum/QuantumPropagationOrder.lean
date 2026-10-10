import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPropagationSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRebitDiagonal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRebitLocal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPropagationTable

namespace OAI

/-! The actual ordered support has its reference bit first, followed by
the duplicate-free propagation support in its literal source order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationOrder
open QuantumOrderedSupport
open scoped Classical

def term (c : QMACircuit) (t : Fin c.gates.length) : QMACircuitTerm c :=
  .inr (.inr (.inr (.inr t)))

theorem sites_eq (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    sites c hT (.inl i)=.inl i :: (QuantumPropagationSupport.sites c t).map Sum.inr := by
  change ((.inl i :: (distributedSites c (qmaFirstUseTime c)
    (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).map Sum.inr) : List (Qubit c)).dedup=_
  rw [ht]
  change ((.inl i :: (propagationSites c t).map Sum.inr) : List (Qubit c)).dedup=_
  rw [List.dedup_cons_of_notMem (by simp),List.dedup_map_of_injective Sum.inr_injective]
  rfl

theorem length_eq (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    (sites c hT (.inl i)).length=(QuantumPropagationSupport.sites c t).length+1 := by
  simp only [sites_eq c hT i t ht,List.length_cons,List.length_map]

def firstIndex (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    Fin (sites c hT (.inl i)).length :=
  ⟨0,by rw [length_eq c hT i t ht]; omega⟩

def nextIndex (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (j : Fin (QuantumPropagationSupport.sites c t).length) :
    Fin (sites c hT (.inl i)).length :=
  ⟨j.val+1,by rw [length_eq c hT i t ht]; omega⟩

theorem firstIndex_site (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t) :
    (supportEquiv c hT (.inl i) (firstIndex c hT i t ht)).val=.inl i := by
  rw [supportEquiv_apply]
  change (sites c hT (.inl i))[0]'(firstIndex c hT i t ht).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_zero]

theorem nextIndex_site (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (j : Fin (QuantumPropagationSupport.sites c t).length) :
    (supportEquiv c hT (.inl i) (nextIndex c hT i t ht j)).val=
      .inr (QuantumPropagationSupport.supportEquiv c t j).val := by
  rw [supportEquiv_apply,QuantumPropagationSupport.supportEquiv_apply]
  change (sites c hT (.inl i))[j.val+1]'(nextIndex c hT i t ht j).isLt=_
  simp only [sites_eq c hT i t ht,List.getElem_cons_succ,List.getElem_map,
    List.get_eq_getElem]

def referenceBit (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) : Fin 2 :=
  s (firstIndex c hT i t ht)

def localBits (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    Fin (QuantumPropagationSupport.sites c t).length → Fin 2 :=
  fun j => s (nextIndex c hT i t ht j)

theorem extend_reference (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inl=
      QuantumAlgebraicHistory.referenceState (qmaHistoryReferenceWork c+1) i
        (referenceBit c hT i t ht s) := by
  funext j
  by_cases hj : j=i
  · subst j
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (firstIndex c hT i t ht)
    rw [firstIndex_site c hT i t ht] at he
    simpa [QuantumAlgebraicHistory.referenceState,referenceBit] using he
  · have hn : Sum.inl j ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      rw [← rawSites_finset] at hm
      have hl := List.mem_toFinset.mp hm
      change Sum.inl j ∈ Sum.inl i :: _ at hl
      rcases List.mem_cons.mp hl with he | he
      · exact hj (Sum.inl_injective he)
      · obtain ⟨q,_,he⟩ := List.mem_map.mp he
        cases he
    have hz : QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inl j)=0 :=
      dite_eq_right hn
    simpa only [Function.comp_apply,QuantumAlgebraicHistory.referenceState,
      ite_eq_right hj] using hz

theorem extend_data (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s ∘ Sum.inr=
      qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) := by
  funext q
  by_cases hq : q∈qmaPropagationSites c t
  · let j := (QuantumPropagationSupport.supportEquiv c t).symm ⟨q,hq⟩
    have hj : (QuantumPropagationSupport.supportEquiv c t j).val=q :=
      congrArg Subtype.val ((QuantumPropagationSupport.supportEquiv c t).apply_symm_apply ⟨q,hq⟩)
    have he := QuantumHistoryDiagonal.orderedExtend_at c hT (.inl i) s
      (nextIndex c hT i t ht j)
    rw [nextIndex_site c hT i t ht,hj] at he
    exact he.trans (show qmaSupportExtend (qmaPropagationSites c t)
      (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=
      s (nextIndex c hT i t ht j) from dite_eq_left hq).symm
  · have hn : Sum.inr q ∉ (qmaOrderedHistoryModel c hT).sites (.inl i) := by
      intro hm
      have hl : Sum.inr q ∈ (sites c hT (.inl i)).toFinset := by
        rw [sites_finset]
        exact hm
      have hx := List.mem_toFinset.mp hl
      rw [sites_eq c hT i t ht] at hx
      rcases List.mem_cons.mp hx with he | he
      · cases he
      · obtain ⟨r,hr,he⟩ := List.mem_map.mp he
        have hrq : r=q := Sum.inr_injective he
        subst r
        apply hq
        rw [← QuantumPropagationSupport.sites_finset]
        exact List.mem_toFinset.mpr hr
    have hz : qmaSupportExtend (qmaPropagationSites c t)
        (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q)) q=0 :=
      dite_eq_right hq
    exact (show QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s (.inr q)=0 from
      dite_eq_right hn).trans hz.symm

theorem ordered_entry (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.propagationCore c t
            (fun q => localBits c hT i t ht s ((QuantumPropagationSupport.supportEquiv c t).symm q))
            (fun q => localBits c hT i t ht r ((QuantumPropagationSupport.supportEquiv c t).symm q)))) := by
  let S := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) s
  let R := QuantumHistoryDiagonal.orderedExtend c hT (.inl i) r
  change QuantumAlgebraicHistory.rebit (qmaHistoryReferenceWork c+1) i
    (QuantumAlgebraicHistory.distributed c (qmaFirstUseTime c)
      (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)) S R=_
  rw [QuantumAlgebraicHistory.rebit_entry_of_references _ _ _ _ _ _ _
    (extend_reference c hT i t ht s) (extend_reference c hT i t ht r)]
  rw [ht]
  change QuantumAlgebraicHistory.oneReference _ _
    (QuantumAlgebraicScalar.mul _ (QuantumAlgebraicHistory.lift _ _
      (S ∘ Sum.inr) (R ∘ Sum.inr)))=_
  have hs := extend_data c hT i t ht s
  have hr := extend_data c hT i t ht r
  change S ∘ Sum.inr=_ at hs
  change R ∘ Sum.inr=_ at hr
  rw [hs,hr,QuantumAlgebraicHistory.lift_extend]

theorem ordered_gram_entry (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=term c t)
    (s r : Fin (sites c hT (.inl i)).length → Fin 2) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i) s r=
      QuantumAlgebraicHistory.oneReference
        (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
        (QuantumAlgebraicScalar.mul
          (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ))
          (QuantumAlgebraicHistory.matMul
            (QuantumAlgebraicHistory.adjoint
              (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
                (c,t.val,QuantumPropagationSupport.labels c t)))
            (QuantumPropagationTable.table (QuantumPropagationSupport.sites c t).length
              (c,t.val,QuantumPropagationSupport.labels c t))
            (localBits c hT i t ht s) (localBits c hT i t ht r))) := by
  rw [ordered_entry c hT i t ht]
  have hg := congrFun (congrFun (QuantumPropagationTable.gram_actual c t)
    (localBits c hT i t ht s)) (localBits c hT i t ht r)
  exact congrArg (fun z => QuantumAlgebraicHistory.oneReference
    (referenceBit c hT i t ht s) (referenceBit c hT i t ht r)
    (QuantumAlgebraicScalar.mul
      (QuantumAlgebraicScalar.rat ((14*(c.work+1)+8)*c.gates.length : ℚ)) z)) hg.symm

end ContinuumCoulomb.QuantumPropagationOrder

end

end OAI
