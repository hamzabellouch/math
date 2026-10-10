import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMerge
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFiniteMembership
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalSumProgram

namespace OAI

/-! Literal polynomial pair-table enumeration and rational accumulation for
canonical bond merging. The vertex count is represented in unary. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListMerge
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

abbrev Input := ℕ × List Bond
def inputCode : Input → List Bool := prodCode unaryCode (listCode bondCode)

noncomputable def orderedProgram : Procedure bondCode pairCode ordered := by
  let a := Procedure.first Nat.bits (prodCode Nat.bits ratCode)
  let b := (Procedure.first Nat.bits ratCode).comp
    (Procedure.second Nat.bits (prodCode Nat.bits ratCode))
  let h := Procedure.binaryLe.comp (a.pair b)
  exact ((Procedure.conditional h a b).pair (Procedure.conditional h b a)).congrFun (by
    intro e
    by_cases he : e.1 ≤ e.2.1
    · simp [ordered,he]
    · have hge : e.2.1 ≤ e.1 := by omega
      simp [ordered,he,hge])

noncomputable def rowProgram : Procedure (prodCode unaryCode Nat.bits) (listCode pairCode)
    (fun x => (List.range x.1).map (fun j => (x.2,j))) :=
  Procedure.tabulate (f := fun i j => (i,j)) (0,0)
    ((Procedure.second unaryCode Nat.bits).pair
      (Procedure.unaryToBits.comp (Procedure.first unaryCode Nat.bits)))

noncomputable def pairsProgram : Procedure unaryCode (listCode pairCode) pairs := by
  let step := rowProgram.comp ((Procedure.second unaryCode unaryCode).pair
    (Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)))
  let table := (Procedure.tabulate (f := fun n i => (List.range n).map (fun j => (i,j))) [] step).comp
    ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))
  exact ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp table).congrFun (by
    intro n
    simp only [Function.comp_apply,pairs,List.product,List.flatMap_def,id_eq])

private noncomputable def filterProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode)
      (fun x => x.2.filter (fun p => decide (p ∈ x.1))) := by
  let key := Procedure.second (listCode pairCode) pairCode
  let keys := Procedure.first (listCode pairCode) pairCode
  let member := QuantumFiniteMembership.pairMemberProgram.comp (key.pair keys)
  let one := (Procedure.listCons pairCode).comp
    (key.pair (Procedure.constant _ (listCode pairCode) []))
  let chunk : Procedure (prodCode (listCode pairCode) pairCode) (listCode pairCode)
      (fun x => if x.2 ∈ x.1 then [x.2] else []) :=
    (Procedure.conditional member one (Procedure.constant _ (listCode pairCode) [])).congrFun (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq])
  let chunks := Procedure.listMapWith (ea := listCode pairCode) (eb := pairCode)
    (ec := listCode pairCode) (f := fun keys p => if p ∈ keys then [p] else []) (0,0) [] chunk
  refine ((QuantumRawExchange.flattenProgram pairCode (0,0)).comp chunks).congrFun ?_
  intro x
  rcases x with ⟨keys,ps⟩
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    by_cases h : p ∈ keys <;> simpa [h] using ih

noncomputable def supportProgram : Procedure inputCode (listCode pairCode)
    (fun x => support x.1 x.2) :=
  filterProgram.comp
    (((Procedure.listMap zeroBond (0,0) orderedProgram).comp (Procedure.second _ _)).pair
      (pairsProgram.comp (Procedure.first _ _)))

noncomputable def weightProgram : Procedure (prodCode pairCode (listCode bondCode)) ratCode
    (fun x => weight x.2 x.1) := by
  let p := Procedure.first pairCode bondCode
  let e := Procedure.second pairCode bondCode
  let h := QuantumFiniteMembership.pairEqProgram.comp ((orderedProgram.comp e).pair p)
  let w := (Procedure.second Nat.bits ratCode).comp
    ((Procedure.second Nat.bits (prodCode Nat.bits ratCode)).comp e)
  let one : Procedure (prodCode pairCode bondCode) ratCode
      (fun x => if ordered x.2=x.1 then x.2.2.2 else 0) :=
    (Procedure.conditional h w (Procedure.constant _ ratCode 0)).congrFun (by
      intro x
      simp only [Function.comp_apply,decide_eq_true_eq])
  exact RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := pairCode) (eb := bondCode) (ec := ratCode)
      (f := fun p e => if ordered e=p then e.2.2 else 0) zeroBond 0 one)

noncomputable def valueProgram : Procedure inputCode (listCode bondCode)
    (fun x => value x.1 x.2) := by
  let xs := Procedure.first (listCode bondCode) pairCode
  let p := Procedure.second (listCode bondCode) pairCode
  let a := (Procedure.first Nat.bits Nat.bits).comp p
  let b := (Procedure.second Nat.bits Nat.bits).comp p
  let w := weightProgram.comp (p.pair xs)
  let entry := a.pair (b.pair w)
  exact (Procedure.listMapWith (ea := listCode bondCode) (eb := pairCode) (ec := bondCode)
    (f := fun xs p => (p.1,p.2,weight xs p)) (0,0) zeroBond entry).comp
      ((Procedure.second _ _).pair supportProgram)

end ContinuumCoulomb.QuantumListMerge

end

end OAI
