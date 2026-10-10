import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawProgram

namespace OAI

/-! Complete polynomial evaluation of each rational X/Z instruction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

noncomputable opaque counterLeftCoefficientProgram (e : Fin 3) : Procedure inputCode ratCode
    (fun x => fieldValue x.1.1 (axis x.2.2.2.1.1)
      (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (counterFieldAProgram a b e).comp radialProgram))

noncomputable opaque counterRightCoefficientProgram (e : Fin 3) : Procedure inputCode ratCode
    (fun x => fieldValue x.1.1 (axis x.2.2.2.1.2)
      (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (counterFieldBProgram a b e).comp radialProgram))

noncomputable opaque counterLeftBondProgram (e : Fin 3) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.1,4*x.2.2.1.1+(qmaFieldEdgeRight e).val,
      fieldValue x.1.1 (axis x.2.2.2.1.1)
        (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e)) :=
  baseLeftProgram.pair ((shiftedLeftProgram _).pair (counterLeftCoefficientProgram e))

noncomputable opaque counterRightBondProgram (e : Fin 3) : Procedure inputCode bondCode
    (fun x => (4*x.2.2.1.2,4*x.2.2.1.2+(qmaFieldEdgeRight e).val,
      fieldValue x.1.1 (axis x.2.2.2.1.2)
        (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) e)) :=
  baseRightProgram.pair ((shiftedRightProgram _).pair (counterRightCoefficientProgram e))

noncomputable opaque counterLeftProgram : Procedure inputCode (listCode bondCode)
    (fun x => field x.1.1 x.2.2.1.1 (axis x.2.2.2.1.1)
      (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2)) :=
  fixedListProgram inputCode bondCode 3 _ counterLeftBondProgram

noncomputable opaque counterRightProgram : Procedure inputCode (listCode bondCode)
    (fun x => field x.1.1 x.2.2.1.2 (axis x.2.2.2.1.2)
      (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2)) :=
  fixedListProgram inputCode bondCode 3 _ counterRightBondProgram

noncomputable opaque pairProgram : Procedure inputCode (listCode bondCode)
    (fun x => cross x.1.1 x.1.2 x.2.2.1.1 x.2.2.1.2
      (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2 ++
      field x.1.1 x.2.2.1.1 (axis x.2.2.2.1.1)
        (counterA x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) ++
      field x.1.1 x.2.2.1.2 (axis x.2.2.2.1.2)
        (counterB x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2)) :=
  (Procedure.listAppend bondCode zeroBond).comp
    (((Procedure.listAppend bondCode zeroBond).comp (crossProgram.pair counterLeftProgram)).pair
      counterRightProgram)

noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) bonds :=
  (Procedure.conditional pairFlagProgram pairProgram
    (Procedure.conditional fieldFlagProgram fieldProgram (Procedure.constant inputCode (listCode bondCode) []))).congrFun
      (by intro x; rfl)

noncomputable opaque offsetProgram : Procedure inputCode ratCode
    (fun x => offset x.1.1 (axis x.2.2.2.1.1) (axis x.2.2.2.1.2) x.2.2.2.2) :=
  selectAxis axisLeftProgram (fun a => selectAxis axisRightProgram
    (fun b => (QuantumAxisSample.offsetProgram a b).comp radialProgram))

noncomputable opaque fieldShiftProgram : Procedure inputCode ratCode
    (fun x => shiftValue (axis x.2.2.2.1.1) x.2.2.2.2) :=
  selectAxis axisLeftProgram (fun a => (shiftValueProgram a).comp weightProgram)

noncomputable opaque scalarProgram : Procedure inputCode ratCode scalar :=
  (Procedure.conditional pairFlagProgram (Procedure.ratNeg.comp offsetProgram)
    (Procedure.conditional fieldFlagProgram (Procedure.ratNeg.comp fieldShiftProgram) weightProgram)).congrFun
      (by intro x; rfl)

noncomputable def termCertificate : Turing.TM2ComputableInPolyTime inputCode
    (prodCode (listCode bondCode) ratCode) (fun x => (bonds x,scalar x)) :=
  (bondsProgram.pair scalarProgram).toTM2

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
