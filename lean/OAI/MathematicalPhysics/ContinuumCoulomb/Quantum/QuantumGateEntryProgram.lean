import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryBitProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGateScalarReduction

namespace OAI

/-! Exact gate entries from a bounded register scan.  Work is unary, addresses
and support labels are binary, and each quantum bit is read from the supplied
small support table.  No sum over ambient configurations occurs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateEntryProgram
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumCircuitCode
open scoped Classical

abbrev Input := ℕ × (ℕ × (QMAGate × QuantumHistoryBitProgram.Data))
def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))

def left (x : Input) : ℕ := gateLeft x.2.2.1 % (x.1+1)
def right (x : Input) : ℕ := gateRight x.2.2.1 % (x.1+1)
def row (x : Input) (k : ℕ) : Fin 2 := QuantumHistoryBitProgram.row x.2.2.2 (x.2.1+k)
def column (x : Input) (k : ℕ) : Fin 2 := QuantumHistoryBitProgram.column x.2.2.2 (x.2.1+k)

def point (x : Input) (k : ℕ) : Bool :=
  if gateTag x.2.2.1 = 2 then
    decide ((row x k).val =
      if k = right x ∧ (column x (left x)).val = 1 then
        1-(column x k).val else (column x k).val)
  else decide (k=left x) || decide ((row x k).val=(column x k).val)

def allWork (x : Input) : Bool := ((List.range (x.1+1)).map (point x)).all id

theorem allWork_iff (x : Input) : allWork x = true ↔
    ∀ i : Fin (x.1+1), point x i.val = true := by
  simp only [allWork,List.all_map,List.all_eq_true,List.mem_range,Function.comp_apply,id_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem allWork_single (x : Input) (hg : gateTag x.2.2.1 ≠ 2) :
    allWork x = true ↔ ∀ i : Fin (x.1+1),
      i ≠ qmaQubit x.1 (gateLeft x.2.2.1) → row x i.val=column x i.val := by
  rw [allWork_iff]
  simp only [point,ite_eq_right hg,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro h i hi
    rcases h i with he | he
    · exact False.elim (hi (Fin.ext he))
    · exact Fin.ext he
  · intro h i
    by_cases hi : i=qmaQubit x.1 (gateLeft x.2.2.1)
    · exact Or.inl (congrArg Fin.val hi)
    · exact Or.inr (congrArg Fin.val (h i hi))

private theorem swap_val (b : Fin 2) : (Equiv.swap (0 : Fin 2) 1 b).val = 1-b.val := by
  fin_cases b <;> decide

theorem allWork_cnot (work base a b : ℕ) (d : QuantumHistoryBitProgram.Data) :
    allWork (work,base,.controlledNot a b,d) = true ↔
      (fun i : Fin (work+1) => row (work,base,.controlledNot a b,d) i.val) =
      qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun i => column (work,base,.controlledNot a b,d) i.val) := by
  rw [allWork_iff,funext_iff]
  apply forall_congr'
  intro i
  change decide ((row (work,base,.controlledNot a b,d) i.val).val =
    if i.val=b%(work+1) ∧ (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 then
      1-(column (work,base,.controlledNot a b,d) i.val).val
    else (column (work,base,.controlledNot a b,d) i.val).val)=true ↔ _
  rw [decide_eq_true_eq]
  have ht : (i.val=b%(work+1)) ↔ i=qmaQubit work b :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have hc : (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1 ↔
      column (work,base,.controlledNot a b,d) (a%(work+1))=1 :=
    ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  have he : (i.val=b%(work+1) ∧
      (column (work,base,.controlledNot a b,d) (a%(work+1))).val=1) ↔
      (i=qmaQubit work b ∧
        column (work,base,.controlledNot a b,d) (a%(work+1))=1) := and_congr ht hc
  by_cases h : i=qmaQubit work b ∧
      column (work,base,.controlledNot a b,d) (a%(work+1))=1
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        Equiv.swap (0:Fin 2) 1 (column (work,base,.controlledNot a b,d) i.val) :=
      ite_eq_left h
    rw [ite_eq_left (he.mpr h),hr,Fin.ext_iff,swap_val]
  · have hr : qmaControlledNot work (qmaQubit work a) (qmaQubit work b)
        (fun j => column (work,base,.controlledNot a b,d) j.val) i =
        column (work,base,.controlledNot a b,d) i.val := ite_eq_right h
    rw [ite_eq_right (mt he.mp h),hr,Fin.ext_iff]

def entry (x : Input) : Scalar :=
  if allWork x then
    if gateTag x.2.2.1=0 then
      QuantumAlgebraicHistory.hadamard (row x (left x)) (column x (left x))
    else if gateTag x.2.2.1=1 then
      QuantumAlgebraicHistory.phaseT (row x (left x)) (column x (left x))
    else rat 1
  else rat 0

theorem entry_eq (work base : ℕ) (g : QMAGate) (d : QuantumHistoryBitProgram.Data) :
    entry (work,base,g,d) = QuantumAlgebraicHistory.gate work g
      (fun i => row (work,base,g,d) i.val) (fun i => column (work,base,g,d) i.val) := by
  cases g with
  | hadamard j =>
    rw [QuantumGateScalarReduction.hadamard_entry]
    have hh := allWork_single (work,base,.hadamard j,d) (by change (0 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.hadamard j,d)=true
    · have hv : entry (work,base,.hadamard j,d) = QuantumAlgebraicHistory.hadamard
          (row (work,base,.hadamard j,d) (left (work,base,.hadamard j,d)))
          (column (work,base,.hadamard j,d) (left (work,base,.hadamard j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.hadamard j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | phaseT j =>
    rw [QuantumGateScalarReduction.phaseT_entry]
    have hh := allWork_single (work,base,.phaseT j,d) (by change (1 : ℕ) ≠ 2; decide)
    by_cases h : allWork (work,base,.phaseT j,d)=true
    · have hv : entry (work,base,.phaseT j,d) = QuantumAlgebraicHistory.phaseT
          (row (work,base,.phaseT j,d) (left (work,base,.phaseT j,d)))
          (column (work,base,.phaseT j,d) (left (work,base,.phaseT j,d))) := by
        unfold entry
        rw [ite_eq_left h]
        rw [ite_eq_right (by change (1 : ℕ) ≠ 0; decide)]
        exact ite_eq_left rfl
      refine hv.trans ?_
      symm
      exact ite_eq_left (hh.mp h)
    · have hv : entry (work,base,.phaseT j,d)=rat 0 := ite_eq_right h
      refine hv.trans ?_
      symm
      exact ite_eq_right (mt hh.mpr h)
  | controlledNot a b =>
    have hh := allWork_cnot work base a b d
    unfold entry QuantumAlgebraicHistory.gate
    simp only [gateTag]
    by_cases h : allWork (work,base,.controlledNot a b,d)=true
    · simp [h,hh.mp h]
    · have hn := mt hh.mpr h
      simp [h,hn]

noncomputable opaque leftProgram : Procedure inputCode Nat.bits left := by
  let work := Procedure.unaryToBits.comp
    (Procedure.first unaryCode (prodCode Nat.bits
      (prodCode gateCode QuantumHistoryBitProgram.dataCode)))
  let tail := Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))
  let tail' := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let gate := (Procedure.first gateCode QuantumHistoryBitProgram.dataCode).comp tail'
  exact Procedure.binaryMod.comp ((gateLeftProgram.comp gate).pair
    (Procedure.successor.comp work))

noncomputable opaque rightProgram : Procedure inputCode Nat.bits right := by
  let work := Procedure.unaryToBits.comp
    (Procedure.first unaryCode (prodCode Nat.bits
      (prodCode gateCode QuantumHistoryBitProgram.dataCode)))
  let tail := Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))
  let tail' := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let gate := (Procedure.first gateCode QuantumHistoryBitProgram.dataCode).comp tail'
  exact Procedure.binaryMod.comp ((gateRightProgram.comp gate).pair
    (Procedure.successor.comp work))

abbrev PointInput := Input × ℕ
def pointCode : PointInput → List Bool := prodCode inputCode Nat.bits

noncomputable opaque queryProgram : Procedure pointCode QuantumHistoryBitProgram.queryCode
    (fun p => (p.1.2.1+p.2,p.1.2.2.2)) := by
  let x := Procedure.first inputCode Nat.bits
  let k := Procedure.second inputCode Nat.bits
  let tail := (Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))).comp x
  let base := (Procedure.first Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let rest := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  let d := (Procedure.second gateCode QuantumHistoryBitProgram.dataCode).comp rest
  exact (Procedure.binaryAdd.comp (base.pair k)).pair d

noncomputable opaque pointRowProgram : Procedure pointCode Nat.bits
    (fun p => (row p.1 p.2).val) := QuantumHistoryBitProgram.rowProgram.comp queryProgram

noncomputable opaque pointColumnProgram : Procedure pointCode Nat.bits
    (fun p => (column p.1 p.2).val) := QuantumHistoryBitProgram.columnProgram.comp queryProgram

noncomputable opaque tagProgram : Procedure inputCode Nat.bits (fun x => gateTag x.2.2.1) := by
  let tail := Procedure.second unaryCode
    (prodCode Nat.bits (prodCode gateCode QuantumHistoryBitProgram.dataCode))
  let rest := (Procedure.second Nat.bits
    (prodCode gateCode QuantumHistoryBitProgram.dataCode)).comp tail
  exact gateTagProgram.comp
    ((Procedure.first gateCode QuantumHistoryBitProgram.dataCode).comp rest)

noncomputable opaque pointProgram : Procedure pointCode Procedure.boolCode
    (fun p => point p.1 p.2) := by
  let x := Procedure.first inputCode Nat.bits
  let k := Procedure.second inputCode Nat.bits
  let l := leftProgram.comp x
  let r := rightProgram.comp x
  let s := pointRowProgram
  let t := pointColumnProgram
  let control := pointColumnProgram.comp (x.pair l)
  let one := Procedure.constant pointCode Nat.bits 1
  let tag := tagProgram.comp x
  let hit := Procedure.boolAnd.comp
    ((Procedure.binaryEq.comp (k.pair r)).pair (Procedure.binaryEq.comp (control.pair one)))
  let flipped := Procedure.binarySub.comp (one.pair t)
  let expected := Procedure.conditional hit flipped t
  let cnot := Procedure.binaryEq.comp (s.pair expected)
  let single := Procedure.boolOr.comp
    ((Procedure.binaryEq.comp (k.pair l)).pair (Procedure.binaryEq.comp (s.pair t)))
  exact (Procedure.conditional (Procedure.binaryEq.comp
    (tag.pair (Procedure.constant pointCode Nat.bits 2))) cnot single).congrFun (by
      intro p
      simp only [Function.comp_apply,point,decide_eq_true_eq,Bool.and_eq_true])

noncomputable opaque allWorkProgram : Procedure inputCode Procedure.boolCode allWork := by
  let testAt : Procedure (prodCode unaryCode inputCode) Procedure.boolCode
      (fun p => point p.2 p.1) :=
    pointProgram.comp ((Procedure.second unaryCode inputCode).pair
      (Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)))
  let count := Procedure.unarySuccessor.comp
    (Procedure.first unaryCode (prodCode Nat.bits
      (prodCode gateCode QuantumHistoryBitProgram.dataCode)))
  exact (QuantumHistoryBitProgram.allProgram.comp
    ((Procedure.tabulate (f := point) false testAt).comp
      (count.pair (Procedure.identity inputCode)))).congrFun (by intro x; rfl)

noncomputable opaque entryProgram : Procedure inputCode scalarCode entry := by
  let x := Procedure.identity inputCode
  let query := x.pair leftProgram
  let values := (pointRowProgram.comp query).pair (pointColumnProgram.comp query)
  let h := (QuantumHistoryBitProgram.matrixEntryProgram QuantumAlgebraicHistory.hadamard).comp values
  let t := (QuantumHistoryBitProgram.matrixEntryProgram QuantumAlgebraicHistory.phaseT).comp values
  let one := Procedure.constant inputCode scalarCode (rat 1)
  let zero := Procedure.constant inputCode scalarCode (rat 0)
  let isH := Procedure.binaryEq.comp (tagProgram.pair (Procedure.constant inputCode Nat.bits 0))
  let isT := Procedure.binaryEq.comp (tagProgram.pair (Procedure.constant inputCode Nat.bits 1))
  exact (Procedure.conditional allWorkProgram
    (Procedure.conditional isH h (Procedure.conditional isT t one)) zero).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,entry,decide_eq_true_eq,QuantumHistoryBitProgram.matrixEntry]
      have hs : QuantumHistoryBitProgram.bit (row x (left x)).val=row x (left x) := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (Fin.isLt _)
      have ht : QuantumHistoryBitProgram.bit (column x (left x)).val=column x (left x) := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (Fin.isLt _)
      rw [hs,ht])

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode scalarCode entry := entryProgram.toTM2

theorem entry_on_support (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (s t : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) (g : QMAGate) :
    entry (c.work,qmaHistoryReferenceWork c+1+(c.gates.length+2),g,
      QuantumOrderedSupport.encodedSites c hT a,
      QuantumSupportLookup.supportBits c hT a s,
      QuantumSupportLookup.supportBits c hT a t) =
    QuantumAlgebraicHistory.gate c.work g
      (fun i => qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => s ((QuantumOrderedSupport.supportEquiv c hT a).symm j))
        (.inr (.inr i)))
      (fun i => qmaSupportExtend ((qmaOrderedHistoryModel c hT).sites a)
        (fun j => t ((QuantumOrderedSupport.supportEquiv c hT a).symm j))
        (.inr (.inr i))) := by
  rw [entry_eq]
  congr 1
  · funext i
    simpa only [row,QuantumOrderedSupport.siteNumber] using
      QuantumHistoryBitProgram.row_actual c hT a s t (.inr (.inr i))
  · funext i
    simpa only [column,QuantumOrderedSupport.siteNumber] using
      QuantumHistoryBitProgram.column_actual c hT a s t (.inr (.inr i))

end ContinuumCoulomb.QuantumGateEntryProgram

end

end OAI
