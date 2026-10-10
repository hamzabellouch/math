import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDescriptorProgram

namespace OAI

/-! Numeric time grouping agrees with the exact ordered reference family.
The first-use time is computed from the actual gate list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

def timeValue (c : QMACircuit) (a : Descriptor) : ℕ :=
  if a.1=0 then min a.2 (c.gates.length-1) else
  if a.1=1 then (if a.2=0 then 0 else c.gates.length-1) else
  if a.1=2 then min (QuantumFirstUseProgram.value (c,a.2)) (c.gates.length-1) else
  if a.1=3 then c.gates.length-1 else a.2

theorem time_encode (c : QMACircuit) (hT : 0<c.gates.length) (a : QMACircuitTerm c) :
    timeValue c (encode c a) =
      (qmaHistoryTermTime c hT (qmaFirstUseTime c) a).val := by
  rcases a with i | (b | (i | (u | t)))
  · rfl
  · fin_cases b
    · simp only [timeValue,encode,qmaHistoryTermTime]
      norm_num
    · simp only [timeValue,encode,qmaHistoryTermTime,qmaBoundedClockTime]
      have he : min c.gates.length (c.gates.length-1)=c.gates.length-1 :=
        min_eq_right (Nat.sub_le _ _)
      norm_num [he]
  · simp only [timeValue,encode,qmaHistoryTermTime,qmaBoundedClockTime]
    norm_num only
    rw [QuantumFirstUseProgram.value_eq]
    rfl
  · cases u
    simp only [timeValue,encode,qmaHistoryTermTime,qmaBoundedClockTime]
    have he : min c.gates.length (c.gates.length-1)=c.gates.length-1 :=
      min_eq_right (Nat.sub_le _ _)
    norm_num [he]
  · simp only [timeValue,encode,qmaHistoryTermTime]
    norm_num

def bucket (c : QMACircuit) (t : ℕ) : List Descriptor :=
  (source c).filter (fun a => decide (timeValue c a=t))

def ordered (c : QMACircuit) : List Descriptor :=
  (List.range c.gates.length).flatMap (bucket c)

theorem bucket_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (t : Fin c.gates.length) :
    bucket c t.val =
      ((qmaHistoryTermList c).filter
        (fun a => decide (qmaHistoryTermTime c hT (qmaFirstUseTime c) a=t))).map
        (encode c) := by
  rw [bucket,source_actual,List.filter_map]
  congr 1
  apply List.filter_congr
  intro a _
  change decide (timeValue c (encode c a)=t.val) = _
  rw [time_encode c hT]
  simp only [Fin.ext_iff]

theorem ordered_actual (c : QMACircuit) (hT : 0<c.gates.length) :
    ordered c=(qmaOrderedHistoryTerms c hT (qmaFirstUseTime c)).map (encode c) := by
  unfold ordered qmaOrderedHistoryTerms qmaGroupByTime
  rw [List.map_flatMap]
  have hr : List.range c.gates.length =
      (List.ofFn (fun t : Fin c.gates.length => t)).map Fin.val := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_range,List.getElem_map,List.getElem_ofFn]
  rw [hr,List.flatMap_map]
  apply List.flatMap_congr
  intro t _
  exact bucket_actual c hT t

theorem ordered_length (c : QMACircuit) (hT : 0<c.gates.length) :
    (ordered c).length=qmaHistoryReferenceWork c+1 := by
  rw [ordered_actual c hT,List.length_map,qmaOrderedHistoryTerms_length]

theorem ordered_get (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) :
    (ordered c)[i.val]'(by rw [ordered_length c hT]; exact i.isLt) =
      encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i) := by
  simp only [ordered_actual c hT,List.getElem_map,qmaOrderedTermEquiv_get]

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
