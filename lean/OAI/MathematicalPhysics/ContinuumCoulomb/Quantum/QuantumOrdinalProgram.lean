import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrdinalSlots
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathVisitProgram

namespace OAI

/-! A literal ordinal-slot program. For an encoded cell list and a unary
label it counts earlier labels in the same cell; the result agrees with the
bounded injective slots used by the spatial construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrdinalProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

def increment (x : Bool × ℕ) : ℕ := if x.1 then x.2+1 else x.2

theorem fold_increment (xs : List Bool) (k : ℕ) :
    xs.foldl (fun n b => increment (b,n)) k = k+xs.countP id := by
  induction xs generalizing k with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons,ih,List.countP_cons]
    cases b <;> simp [increment,Nat.add_comm,Nat.add_left_comm]

noncomputable def incrementProgram :
    Procedure (prodCode Procedure.boolCode unaryCode) unaryCode increment := by
  let k := Procedure.second Procedure.boolCode unaryCode
  exact (Procedure.conditional (Procedure.first Procedure.boolCode unaryCode)
    (Procedure.unarySuccessor.comp k) k).congrFun (by intro x; rfl)

noncomputable def countProgram :
    Procedure (listCode Procedure.boolCode) unaryCode (fun xs => xs.countP id) := by
  let fold := Procedure.foldList false incrementProgram Polynomial.X (by
    intro xs k i
    rw [fold_increment]
    have hc := List.countP_le_length (p := id) (l := xs.take i)
    have ht : (xs.take i).length ≤ xs.length := List.length_take_le' _ _
    have hs := list_length_le_code Procedure.boolCode xs
    simp only [unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  exact (fold.comp ((Procedure.identity _).pair
    (Procedure.constant _ unaryCode 0))).congrFun (by
      intro xs
      simp only [Function.comp_apply,id_eq,fold_increment,zero_add])

abbrev Input := ℕ × List Pair
def inputCode : Input → List Bool := prodCode unaryCode (listCode pairCode)

def sameCell (x : Input) (i : ℕ) : Bool :=
  decide (QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)

def value (x : Input) : ℕ := ((List.range x.1).map (sameCell x)).countP id

noncomputable def sameCellProgram :
    Procedure (prodCode unaryCode inputCode) Procedure.boolCode
      (fun x => sameCell x.2 x.1) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode inputCode)
  let env := Procedure.second unaryCode inputCode
  let q := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode (listCode pairCode)).comp env)
  let xs := (Procedure.second unaryCode (listCode pairCode)).comp env
  exact QuantumFiniteMembership.pairEqProgram.comp
    (((Procedure.listGet pairCode (0,0)).comp (i.pair xs)).pair
      ((Procedure.listGet pairCode (0,0)).comp (q.pair xs)))

noncomputable def program : Procedure inputCode unaryCode value :=
  countProgram.comp ((Procedure.tabulate (f := sameCell) false sameCellProgram).comp
    ((Procedure.first unaryCode (listCode pairCode)).pair (Procedure.identity inputCode)))

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode unaryCode value :=
  program.toTM2

theorem value_eq_card (x : Input) :
    value x = ((Finset.range x.1).filter (fun i =>
      QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)).card := by
  unfold value sameCell
  rw [List.countP_map]
  simp only [Function.comp_def,id_eq]
  symm
  simpa only [List.toFinset_range,Function.comp_apply,id_eq] using
    (List.nodup_range (n := x.1)).card_eq_countP
      (P := fun i => QuantumPathVisitProgram.lookup x.2 i = QuantumPathVisitProgram.lookup x.2 x.1)

theorem lookup_ofFn {n : ℕ} (cells : Fin n → Pair) (q : Fin n) :
    QuantumPathVisitProgram.lookup (List.ofFn cells) q.val = cells q := by
  unfold QuantumPathVisitProgram.lookup
  rw [List.headD_eq_head?_getD,List.head?_drop]
  simp

theorem value_ofFn {n : ℕ} (cells : Fin n → Pair) (q : Fin n) :
    value (q.val,List.ofFn cells) = QuantumOrdinalSlots.rank cells q := by
  rw [value_eq_card]
  unfold QuantumOrdinalSlots.rank
  symm
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    obtain ⟨_,hlt,hcell⟩ := Finset.mem_filter.mp hr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hlt,?_⟩
    simpa only [lookup_ofFn] using hcell
  · intro r hr s hs h
    exact Fin.ext h
  · intro i hi
    obtain ⟨hi,hcell⟩ := Finset.mem_filter.mp hi
    have hiq : i < q.val := Finset.mem_range.mp hi
    let r : Fin n := ⟨i,hiq.trans q.isLt⟩
    refine ⟨r,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hiq,?_⟩
    simpa only [← show r.val=i from rfl,lookup_ofFn] using hcell

end ContinuumCoulomb.QuantumOrdinalProgram

end

end OAI
