import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOffsetSample

namespace OAI

/-! Polynomial programs for the counterterm field coefficients and scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque shiftValueProgram (a : Fin 2) : Procedure ratCode ratCode (shiftValue a) := by
  by_cases ha : a = 0
  · exact (Procedure.constant ratCode ratCode 0).congrFun (by intro t; simp [shiftValue,ha])
  · exact (Procedure.ratMul.comp ((Procedure.identity ratCode).pair
      (Procedure.constant ratCode ratCode (1/2)))).congrFun (by
        intro t
        simp only [shiftValue,ha,ite_false,Function.comp_apply,id_eq]
        ring)

noncomputable opaque counterFieldAProgram (a b : Fin 2) (e : Fin 3) :
    Procedure radialCode ratCode (fun x => fieldValue x.1 a (counterA x.1 a b x.2) e) :=
  ((fieldValueProgram a e).comp (inputPrecisionProgram.pair (counterAProgram a b))).congrFun
    (by intro x; rfl)

noncomputable opaque counterFieldBProgram (a b : Fin 2) (e : Fin 3) :
    Procedure radialCode ratCode (fun x => fieldValue x.1 b (counterB x.1 a b x.2) e) :=
  ((fieldValueProgram b e).comp (inputPrecisionProgram.pair (counterBProgram a b))).congrFun
    (by intro x; rfl)

noncomputable opaque offsetProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => offset x.1 a b x.2) := by
  let left := (shiftValueProgram a).comp (counterAProgram a b)
  let right := (shiftValueProgram b).comp (counterBProgram a b)
  let first := Procedure.ratMul.comp ((factorProgram a b).pair (Procedure.constant radialCode ratCode (shift a true)))
  let second := (shiftProgram b).comp inputCoefficientProgram
  let product := Procedure.ratMul.comp (first.pair second)
  exact (Procedure.ratSub.comp ((Procedure.ratAdd.comp (left.pair right)).pair product)).congrFun
    (by intro x; rfl)

noncomputable def offsetCertificate (a b : Fin 2) : Turing.TM2ComputableInPolyTime
    radialCode ratCode (fun x => offset x.1 a b x.2) := (offsetProgram a b).toTM2

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
