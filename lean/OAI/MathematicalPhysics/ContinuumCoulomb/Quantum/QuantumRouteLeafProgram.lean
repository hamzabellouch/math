import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteLeaf
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighborsFour
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawProgram
import OAI.Computability.QuantumFactoring.BitStackOptions

namespace OAI

/-! Literal polynomial TM2 evaluators for scaled centers and reserved leaves. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRouteLeafCode
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable def coordinateProgram (xAxis : Bool) (offset : ℕ) : Procedure pairCode Nat.bits
    (fun p => 8*(if xAxis then p.1 else p.2)+offset) := by
  let p : Procedure pairCode Nat.bits (fun p => if xAxis then p.1 else p.2) := by
    cases xAxis
    · exact Procedure.second Nat.bits Nat.bits
    · exact Procedure.first Nat.bits Nat.bits
  let mul := Procedure.binaryMul.comp ((Procedure.constant pairCode Nat.bits 8).pair p)
  exact (Procedure.binaryAdd.comp (mul.pair (Procedure.constant pairCode Nat.bits offset))).congrFun
    (by intro p; cases xAxis <;> rfl)

noncomputable opaque centerProgram : Procedure pairCode pairCode qmaLeafCenter :=
  (coordinateProgram true 4).pair (coordinateProgram false 4)

noncomputable def leafProgram (a : Fin 4) : Procedure pairCode pairCode (fun p => qmaRouteLeaf p a) := by
  by_cases h0 : a = 0
  · subst a
    exact ((coordinateProgram true 5).pair (coordinateProgram false 5)).congrFun (by intro p; rfl)
  by_cases h1 : a = 1
  · subst a
    exact ((coordinateProgram true 3).pair (coordinateProgram false 5)).congrFun (by intro p; rfl)
  by_cases h2 : a = 2
  · subst a
    exact ((coordinateProgram true 3).pair (coordinateProgram false 3)).congrFun (by intro p; rfl)
  have h3 : a = 3 := by omega
  subst a
  exact ((coordinateProgram true 5).pair (coordinateProgram false 3)).congrFun (by intro p; rfl)

noncomputable opaque leafListProgram : Procedure pairCode (listCode pairCode)
    (fun p => List.ofFn (qmaRouteLeaf p)) :=
  QuantumRawExchange.fixedListProgram pairCode pairCode 4 (fun a p => qmaRouteLeaf p a) leafProgram

abbrev Ends := Pair × Pair
def endsCode : Ends → List Bool := prodCode pairCode pairCode
noncomputable opaque firstProgram : Procedure endsCode pairCode Prod.fst := Procedure.first _ _
noncomputable opaque secondProgram : Procedure endsCode pairCode Prod.snd := Procedure.second _ _
noncomputable def axisProgram (left xAxis : Bool) : Procedure endsCode Nat.bits
    (fun x => if xAxis then (if left then x.1 else x.2).1 else (if left then x.1 else x.2).2) := by
  let p : Procedure endsCode pairCode (fun x => if left then x.1 else x.2) := by
    cases left
    · exact secondProgram
    · exact firstProgram
  let q : Procedure pairCode Nat.bits (fun x => if xAxis then x.1 else x.2) := by
    cases xAxis
    · exact Procedure.second Nat.bits Nat.bits
    · exact Procedure.first Nat.bits Nat.bits
  exact (q.comp p).congrFun (by intro x; cases left <;> cases xAxis <;> rfl)

noncomputable opaque directionProgram : Procedure endsCode Nat.bits
    (fun x => (qmaGridNeighborIndex x.1 x.2).val) := by
  let one := Procedure.constant endsCode Nat.bits 1
  let east := Procedure.binaryEq.comp ((axisProgram false true).pair
    (Procedure.binaryAdd.comp ((axisProgram true true).pair one)))
  let north := Procedure.binaryEq.comp ((axisProgram false false).pair
    (Procedure.binaryAdd.comp ((axisProgram true false).pair one)))
  let west := Procedure.binaryEq.comp ((Procedure.binaryAdd.comp ((axisProgram false true).pair one)).pair
    (axisProgram true true))
  exact (Procedure.conditional east (Procedure.constant endsCode Nat.bits 0)
    (Procedure.conditional north (Procedure.constant endsCode Nat.bits 1)
      (Procedure.conditional west (Procedure.constant endsCode Nat.bits 2)
        (Procedure.constant endsCode Nat.bits 3)))).congrFun
      (by intro x; simp [qmaGridNeighborIndex]; split_ifs <;> rfl)

noncomputable opaque selectedLeafProgram : Procedure endsCode pairCode
    (fun x => qmaRouteLeaf x.1 (qmaGridNeighborIndex x.1 x.2)) := by
  let isZero := Procedure.binaryEq.comp (directionProgram.pair (Procedure.constant endsCode Nat.bits 0))
  let isOne := Procedure.binaryEq.comp (directionProgram.pair (Procedure.constant endsCode Nat.bits 1))
  let isTwo := Procedure.binaryEq.comp (directionProgram.pair (Procedure.constant endsCode Nat.bits 2))
  exact (Procedure.conditional isZero ((leafProgram 0).comp firstProgram)
    (Procedure.conditional isOne ((leafProgram 1).comp firstProgram)
      (Procedure.conditional isTwo ((leafProgram 2).comp firstProgram)
        ((leafProgram 3).comp firstProgram)))).congrFun (by
          intro x
          generalize h : qmaGridNeighborIndex x.1 x.2 = a
          fin_cases a <;> simp [h])

noncomputable def centerCertificate : Turing.TM2ComputableInPolyTime pairCode pairCode qmaLeafCenter :=
  centerProgram.toTM2
noncomputable def selectedLeafCertificate : Turing.TM2ComputableInPolyTime endsCode pairCode
    (fun x => qmaRouteLeaf x.1 (qmaGridNeighborIndex x.1 x.2)) := selectedLeafProgram.toTM2

end ContinuumCoulomb.QuantumRouteLeafCode

end

end OAI
