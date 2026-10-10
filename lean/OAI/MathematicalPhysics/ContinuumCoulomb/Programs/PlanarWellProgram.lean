import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarWellNumerics

namespace OAI

/-! The fixed well profile has an actual rational polynomial-time
evaluator. The positive denominator guard is independent of all inputs. -/

namespace ContinuumCoulomb.PlanarWellNumerics
open ExactQuantumFactoring.BitStackProgram

abbrev Input := ℕ × (ℚ × ℚ)
def inputCode : Input → List Bool := prodCode unaryCode (prodCode ratCode ratCode)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  (Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode (4*guard^2)).pair
    Procedure.unarySuccessor)).congrFun (by intro p; rfl)

noncomputable opaque normSquareProgram : Procedure (prodCode ratCode ratCode) ratCode
    (fun q => q.1^2+q.2^2) := by
  let x := Procedure.first ratCode ratCode
  let y := Procedure.second ratCode ratCode
  let xx := Procedure.ratMul.comp (x.pair x)
  let yy := Procedure.ratMul.comp (y.pair y)
  exact (Procedure.ratAdd.comp (xx.pair yy)).congrFun (by intro q; simp only [pow_two]; rfl)

noncomputable opaque program : Procedure inputCode ratCode
    (fun x => approximate x.1 x.2) := by
  let p := precisionProgram.comp (Procedure.first unaryCode (prodCode ratCode ratCode))
  let q := Procedure.second unaryCode (prodCode ratCode ratCode)
  let r := Procedure.constant inputCode unaryCode 2
  let one := Procedure.constant inputCode ratCode (1:ℚ)
  let zero := Procedure.constant inputCode ratCode (0:ℚ)
  let two := Procedure.constant inputCode ratCode (2:ℚ)
  let norm := normSquareProgram.comp q
  let inside := Procedure.intSign.comp (Procedure.ratNum.comp (Procedure.ratSub.comp (norm.pair one)))
  let forcing := Procedure.ratNeg.comp (PlanarForcingProgram.program.comp q)
  let phi := ResolventSchedule.program.comp ((r.pair p).pair q)
  let sample := Procedure.ratDiv.comp (forcing.pair (Procedure.ratMul.comp (two.pair phi)))
  exact (Procedure.conditional inside sample zero).congrFun (by
    intro x
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq]
    unfold approximate outside
    change (if x.2.1^2+x.2.2^2-1 < 0 then
      -PlanarForcingProgram.value x.2/(2*ResolventSchedule.approximate ((2,precision x.1),x.2))
      else 0) = (if 1 ≤ x.2.1^2+x.2.2^2 then 0 else
      -PlanarForcingProgram.value x.2/(2*ResolventSchedule.approximate ((2,precision x.1),x.2)))
    by_cases hq : 1 ≤ x.2.1^2+x.2.2^2
    · rw [ite_eq_right (by linarith),ite_eq_left hq]
    · rw [ite_eq_left (by linarith),ite_eq_right hq])

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode ratCode
    (fun x => approximate x.1 x.2) := program.toTM2

end ContinuumCoulomb.PlanarWellNumerics

end OAI
