import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCountertermSample
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAxisSampleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.BisectionProgram

namespace OAI

/-! Literal rational arithmetic for the internal four-spin counterterms. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque positiveProgram : Procedure ratCode Procedure.boolCode (fun t : ℚ => decide (0 < t)) :=
  BisectionProgram.rationalLess.comp ((Procedure.constant ratCode ratCode 0).pair (Procedure.identity ratCode))

noncomputable opaque polarityProgram : Procedure ratCode ratCode polarity := by
  exact (Procedure.conditional positiveProgram (Procedure.constant ratCode ratCode (-1))
    (Procedure.constant ratCode ratCode 1)).congrFun (by
      intro t
      by_cases ht : 0 < t
      · simp [polarity,ht,not_le_of_gt ht]
      · simp [polarity,ht,le_of_not_gt ht])

noncomputable opaque shiftProgram (a : Fin 2) : Procedure ratCode ratCode
    (fun t => shift a (decide (t ≤ 0))) := by
  by_cases ha : a = 0
  · exact (Procedure.constant ratCode ratCode 400).congrFun (by intro t; simp [shift,ha])
  · exact (Procedure.conditional positiveProgram (Procedure.constant ratCode ratCode (4/3))
      (Procedure.constant ratCode ratCode (8/3))).congrFun (by
        intro t
        by_cases ht : 0 < t
        · simp [shift,ha,ht,not_le_of_gt ht]
        · simp [shift,ha,ht,le_of_not_gt ht])

noncomputable opaque absoluteInputProgram : Procedure radialCode ratCode (fun x => |x.2|) :=
  MediatorProgram.absoluteProgram.comp inputCoefficientProgram

noncomputable opaque factorProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => factor x.1 a b x.2) := by
  let l := (valueProgram a).comp inputPrecisionProgram
  let r := (valueProgram b).comp inputPrecisionProgram
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (absoluteInputProgram.pair l)).pair r)).congrFun
    (by intro x; rfl)

noncomputable opaque counterAProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => counterA x.1 a b x.2) := by
  let v := (valueProgram b).comp inputPrecisionProgram
  let s := (shiftProgram b).comp inputCoefficientProgram
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (absoluteInputProgram.pair v)).pair s)).congrFun
    (by intro x; rfl)

noncomputable opaque counterBProgram (a b : Fin 2) : Procedure radialCode ratCode
    (fun x => counterB x.1 a b x.2) := by
  let v := (valueProgram a).comp inputPrecisionProgram
  let sign := polarityProgram.comp inputCoefficientProgram
  let initial := Procedure.ratMul.comp (absoluteInputProgram.pair v)
  let signed := Procedure.ratMul.comp (initial.pair sign)
  exact (Procedure.ratMul.comp (signed.pair (Procedure.constant radialCode ratCode (shift a true)))).congrFun
    (by intro x; rfl)

noncomputable def counterACertificate (a b : Fin 2) : Turing.TM2ComputableInPolyTime
    radialCode ratCode (fun x => counterA x.1 a b x.2) := (counterAProgram a b).toTM2

noncomputable def counterBCertificate (a b : Fin 2) : Turing.TM2ComputableInPolyTime
    radialCode ratCode (fun x => counterB x.1 a b x.2) := (counterBProgram a b).toTM2

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
