import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedDescriptors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySiteProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSourceIndex

namespace OAI

/-! The descriptor compiler computes the very same ordered support labels
as the mathematical local-history construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open QuantumHistorySiteProgram

def distributedLabels (c : QMACircuit) (a : Descriptor) : List ℕ :=
  if a.1=0 then [a.2,a.2+1] else
  if a.1=1 then (if a.2=0 then [0] else [c.gates.length+1]) else
  if a.1=2 then
    let t := QuantumFirstUseProgram.value (c,a.2)
    [t,t+1,c.gates.length+2+a.2] else
  if a.1=3 then [c.gates.length,c.gates.length+2+c.work] else
    propagationLabels (c,a.2)

theorem distributedLabels_actual (c : QMACircuit) (a : QMACircuitTerm c) :
    distributedLabels c (encode c a) =
      (QuantumOrderedSupport.distributedSites c (qmaFirstUseTime c) a).map
        (distributedNumber c) := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b <;>
      simp [distributedLabels,encode,QuantumOrderedSupport.distributedSites,distributedNumber]
  · simp only [distributedLabels,encode]
    norm_num only
    rw [QuantumFirstUseProgram.value_eq]
    rfl
  · cases u
    rfl
  · simp only [distributedLabels,encode]
    norm_num only
    exact propagationLabels_actual c t

def referenceWork (c : QMACircuit) : ℕ := 2*c.gates.length+c.work+4

theorem referenceWork_eq (c : QMACircuit) : referenceWork c=qmaHistoryReferenceWork c := rfl

def orderedAt (c : QMACircuit) (i : ℕ) : Descriptor :=
  ((ordered c).drop i).headD (0,0)

theorem orderedAt_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    orderedAt c i.val = encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  unfold orderedAt
  rw [List.headD_eq_head?_getD,List.head?_drop]
  rw [List.getElem?_eq_getElem (by rw [ordered_length c hT]; exact i.isLt)]
  exact ordered_get c hT i

def rebitLabels (c : QMACircuit) (i : ℕ) : List ℕ :=
  i :: (distributedLabels c (orderedAt c i)).map (fun j => referenceWork c+1+j)

def referenceLabels (c : QMACircuit) (i : ℕ) : List ℕ :=
  if i<referenceWork c+1 then rebitLabels c i else
    [i-(referenceWork c+1),i-(referenceWork c+1)+1]

theorem number_inr (c : QMACircuit) (q : QMACircuitQubit c) :
    QuantumOrderedSupport.siteNumber c (.inr q)=
      referenceWork c+1+distributedNumber c q := by
  cases q <;> simp [QuantumOrderedSupport.siteNumber,distributedNumber,referenceWork_eq,
    Nat.add_assoc]

theorem rebitLabels_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    rebitLabels c i.val =
      (QuantumOrderedSupport.rawSites c hT (.inl i)).map
        (QuantumOrderedSupport.siteNumber c) := by
  rw [rebitLabels,orderedAt_actual c hT i,distributedLabels_actual]
  simp only [QuantumOrderedSupport.rawSites,List.map_cons,List.map_map,Function.comp_def,
    QuantumOrderedSupport.siteNumber]
  congr 1
  apply List.map_congr_left
  intro q _
  exact (number_inr c q).symm

theorem referenceLabels_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    referenceLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      (QuantumOrderedSupport.rawSites c hT a).map
        (QuantumOrderedSupport.siteNumber c) := by
  cases a with
  | inl i =>
    change (if i.val<referenceWork c+1 then rebitLabels c i.val else _) = _
    rw [ite_eq_left (by simpa only [referenceWork_eq] using i.isLt)]
    exact rebitLabels_actual c hT i
  | inr i =>
    change referenceLabels c (qmaHistoryReferenceWork c+1+i.val) = _
    rw [referenceLabels,ite_eq_right (by rw [referenceWork_eq]; omega)]
    simp only [referenceWork_eq,Nat.add_sub_cancel_left,QuantumOrderedSupport.rawSites,
      List.map_cons,List.map_nil,QuantumOrderedSupport.siteNumber,Fin.val_castSucc,Fin.val_succ]

def supportLabels (c : QMACircuit) (i : ℕ) : List ℕ := (referenceLabels c i).dedup

theorem supportLabels_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    supportLabels c ((QuantumOrderedSourceIndex.reference c).symm a).val =
      QuantumOrderedSupport.encodedSites c hT a := by
  rw [supportLabels,referenceLabels_actual c hT a,
    List.dedup_map_of_injective (QuantumOrderedSupport.siteNumber_injective c)]
  rfl

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
