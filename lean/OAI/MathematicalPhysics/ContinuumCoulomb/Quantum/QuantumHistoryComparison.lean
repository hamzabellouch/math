import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryBitProgram

namespace OAI

/-! Unary-bounded equality checks for the clock/work registers. A single
specified bit may be flipped, as required by the propagation delta. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryComparison
open ExactQuantumFactoring.BitStackProgram QuantumHistoryBitProgram

abbrev Input := ℕ × (ℕ × (Bool × (ℕ × Data)))
def inputCode : Input → List Bool := prodCode unaryCode
  (prodCode Nat.bits (prodCode Procedure.boolCode (prodCode Nat.bits dataCode)))

def point (x : Input) (k : ℕ) : Bool :=
  decide (row x.2.2.2.2 (x.2.1+k) =
    if x.2.2.1=true ∧ x.2.1+k=x.2.2.2.1 then
      Equiv.swap (0:Fin 2) 1 (column x.2.2.2.2 (x.2.1+k))
    else column x.2.2.2.2 (x.2.1+k))

def value (x : Input) : Bool := ((List.range x.1).map (point x)).all id

theorem value_iff (x : Input) : value x=true ↔
    ∀ i : Fin x.1, row x.2.2.2.2 (x.2.1+i.val) =
      if x.2.2.1=true ∧ x.2.1+i.val=x.2.2.2.1 then
        Equiv.swap (0:Fin 2) 1 (column x.2.2.2.2 (x.2.1+i.val))
      else column x.2.2.2.2 (x.2.1+i.val) := by
  simp only [value,List.all_map,List.all_eq_true,List.mem_range,
    Function.comp_apply,id_eq,point,decide_eq_true_eq]
  exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩

theorem no_flip_iff (count base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      ∀ i : Fin count, row d (base+i.val)=column d (base+i.val) := by
  rw [value_iff]
  simp only [Bool.false_eq_true,false_and,ite_false]

theorem value_equiv_iff {ι : Type} {count : ℕ} (e : ι ≃ Fin count)
    (base target : ℕ) (d : Data) :
    value (count,base,false,target,d)=true ↔
      (fun i => row d (base+(e i).val))=(fun i => column d (base+(e i).val)) := by
  rw [no_flip_iff,funext_iff]
  constructor
  · intro h i
    exact h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact h j

theorem value_flip_iff {ι : Type} [DecidableEq ι] {count : ℕ} (e : ι ≃ Fin count)
    (base : ℕ) (q : ι) (d : Data) :
    value (count,base,true,base+(e q).val,d)=true ↔
      (fun i => row d (base+(e i).val))=
        qmaBitFlip q (fun i => column d (base+(e i).val)) := by
  rw [value_iff,funext_iff]
  have hv (i : ι) (hi : i≠q) : (e i).val≠(e q).val :=
    fun h => hi (e.injective (Fin.ext h))
  constructor
  · intro h i
    by_cases hi : i=q
    · subst i
      simpa [qmaBitFlip] using h (e q)
    · simpa [qmaBitFlip,hi,hv i hi] using h (e i)
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    by_cases hj : j=q
    · subst j
      simpa [qmaBitFlip] using h q
    · simpa [qmaBitFlip,hj,hv j hj] using h j

abbrev PointInput := Input × ℕ
def pointCode : PointInput → List Bool := prodCode inputCode Nat.bits

noncomputable opaque countProgram : Procedure inputCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque baseProgram : Procedure inputCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first _ _).comp (Procedure.second _ _)
noncomputable opaque flipProgram : Procedure inputCode Procedure.boolCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _))
noncomputable opaque targetProgram : Procedure inputCode Nat.bits (fun x => x.2.2.2.1) :=
  (Procedure.first _ _).comp
    ((Procedure.second _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _)))
noncomputable opaque dataProgram : Procedure inputCode dataCode (fun x => x.2.2.2.2) :=
  (Procedure.second _ _).comp
    ((Procedure.second _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _)))

private theorem swap_val (b : Fin 2) : (Equiv.swap (0:Fin 2) 1 b).val=1-b.val := by
  fin_cases b <;> decide

noncomputable opaque pointProgram : Procedure pointCode Procedure.boolCode
    (fun p => point p.1 p.2) := by
  let x := Procedure.first inputCode Nat.bits
  let k := Procedure.second inputCode Nat.bits
  let label := Procedure.binaryAdd.comp ((baseProgram.comp x).pair k)
  let query := label.pair (dataProgram.comp x)
  let r := rowProgram.comp query
  let c := columnProgram.comp query
  let flip := Procedure.boolAnd.comp ((flipProgram.comp x).pair
    (Procedure.binaryEq.comp (label.pair (targetProgram.comp x))))
  let expected := Procedure.conditional flip
    (Procedure.binarySub.comp ((Procedure.constant pointCode Nat.bits 1).pair c)) c
  exact (Procedure.binaryEq.comp (r.pair expected)).congrFun (by
    intro p
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,point,decide_eq_true_eq,Bool.and_eq_true]
    split_ifs <;> simp only [Fin.ext_iff,swap_val])

noncomputable opaque unaryPointProgram :
    Procedure (prodCode unaryCode inputCode) Procedure.boolCode
      (fun x => point x.2 x.1) :=
  pointProgram.comp ((Procedure.second unaryCode inputCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)))

noncomputable opaque program : Procedure inputCode Procedure.boolCode value :=
  (allProgram.comp ((Procedure.tabulate (f := fun x i => point x i) false unaryPointProgram).comp
    (countProgram.pair (Procedure.identity inputCode)))).congrFun (by
      intro x
      simp only [Function.comp_apply,id_eq,value,allBits])

end ContinuumCoulomb.QuantumHistoryComparison

end

end OAI
