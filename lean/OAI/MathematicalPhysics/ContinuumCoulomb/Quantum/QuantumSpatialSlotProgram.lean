import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrdinalProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrdinalSpatial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedEndpointWalk

namespace OAI

/-! The actual fine-grid positions and lane colors of the ordinal-slot model
are computed directly from encoded lists of cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialSlotProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumOrdinalProgram

def fineSite (A : ℕ) (x : Input) : Pair :=
  let p := QuantumPathVisitProgram.lookup x.2 x.1
  (value x+A*p.1,p.2)

def lane (B : ℕ) (x : Input) : ℕ :=
  let p := QuantumPathVisitProgram.lookup x.2 x.1
  value x+B*(p.2%3)+(3*B)*(p.1%3)

noncomputable def cellProgram : Procedure inputCode pairCode
    (fun x => QuantumPathVisitProgram.lookup x.2 x.1) :=
  (Procedure.listGet pairCode (0,0)).comp
    ((Procedure.unaryToBits.comp (Procedure.first unaryCode (listCode pairCode))).pair
      (Procedure.second unaryCode (listCode pairCode)))

noncomputable def fineSiteProgram (A : ℕ) : Procedure inputCode pairCode (fineSite A) := by
  let p := cellProgram
  let row := (Procedure.first Nat.bits Nat.bits).comp p
  let col := (Procedure.second Nat.bits Nat.bits).comp p
  let rank := Procedure.unaryToBits.comp QuantumOrdinalProgram.program
  let x := Procedure.binaryAdd.comp (rank.pair
    (Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits A).pair row)))
  exact x.pair col

noncomputable def laneProgram (B : ℕ) : Procedure inputCode Nat.bits (lane B) := by
  let p := cellProgram
  let row := (Procedure.first Nat.bits Nat.bits).comp p
  let col := (Procedure.second Nat.bits Nat.bits).comp p
  let rem (v : Procedure inputCode Nat.bits (fun x =>
      (QuantumPathVisitProgram.lookup x.2 x.1).1)) :=
    Procedure.binaryMod.comp (v.pair (Procedure.constant inputCode Nat.bits 3))
  let rowTerm := Procedure.binaryMul.comp
    ((Procedure.constant inputCode Nat.bits (3*B)).pair (rem row))
  let colTerm := Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits B).pair
    (Procedure.binaryMod.comp (col.pair (Procedure.constant inputCode Nat.bits 3))))
  let rank := Procedure.unaryToBits.comp QuantumOrdinalProgram.program
  exact Procedure.binaryAdd.comp ((Procedure.binaryAdd.comp (rank.pair colTerm)).pair rowTerm)

theorem colorEquiv_val {B : ℕ} (c : Fin 3 × Fin 3 × Fin B) :
    (qmaGridColorEquiv B c).val = c.2.2.val+B*c.2.1.val+(3*B)*c.1.val := by
  rfl

theorem fineSite_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    {m : ℕ} (labels : M.Term ≃ Fin m) (q : Fin M.n) :
    fineSite A (q.val,List.ofFn (QuantumOrdinalPlacement.coordinates M.cell)) =
      (M.withOrdinalSlots labels).routeVertex q := by
  unfold fineSite
  rw [lookup_ofFn,value_ofFn]
  rfl

theorem lane_actual {A B : ℕ} (M : QMASpatialExchangeModel A B)
    {m : ℕ} (labels : M.Term ≃ Fin m) (e : M.Term) :
    lane B ((labels e).val,
      List.ofFn (QuantumOrdinalPlacement.coordinates (M.anchor ∘ labels.symm))) =
      ((M.withOrdinalSlots labels).laneColor e).val := by
  unfold lane
  rw [lookup_ofFn,value_ofFn]
  change _ = (qmaGridColorEquiv B ((M.withOrdinalSlots labels).termSlots.color e)).val
  rw [colorEquiv_val]
  simp only [QMASpatialExchangeModel.withOrdinalSlots,QMACellSlots.color,
    QMACellSlots.transport,QuantumOrdinalPlacement.slots,QuantumOrdinalPlacement.coordinates,
    Function.comp_apply,Equiv.symm_apply_apply]

end ContinuumCoulomb.QuantumSpatialSlotProgram

end

end OAI
