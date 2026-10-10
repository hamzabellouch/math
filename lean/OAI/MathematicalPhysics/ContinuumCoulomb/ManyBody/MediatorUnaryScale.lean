import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorUnaryPrimitives

namespace OAI

/-! Actual unary programs for the polynomial mediator scale, its square,
and the retained-term and spoke coefficient bounds. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque scale : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.scale x.1 x.2.1 x.2.2.1) := by
  let product : Procedure envCode unaryCode
      (fun x : Env => (x.1 + 1) ^ 3 * x.2.1 ^ 3 * x.2.2.1) :=
    mul.comp (cubicProduct.pair gProgram)
  exact (mul.comp (scaleConstant.pair product)).congrFun
    (by intro x; simp only [Function.comp_apply, MediatorParameters.scale, Nat.mul_assoc])
noncomputable opaque delta : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.delta x.1 x.2.1 x.2.2.1) := by
  let square : Procedure envCode unaryCode (fun x : Env =>
      MediatorParameters.scale x.1 x.2.1 x.2.2.1 * MediatorParameters.scale x.1 x.2.1 x.2.2.1) :=
    mul.comp (scale.pair scale)
  exact square.congrFun (by
    intro x
    exact delta_as_mul x.1 x.2.1 x.2.2.1)

noncomputable opaque retainedBound : Procedure envCode unaryCode
    (fun x : Env => 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1) := by
  let threeR : Procedure envCode unaryCode (fun x : Env => 3 * x.1) := mul.comp ((Procedure.constant envCode unaryCode 3).pair rProgram)
  exact mul.comp (threeR.pair delta)
noncomputable opaque spokeBound : Procedure envCode unaryCode
    (fun x : Env => 2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1) := by
  let twice : Procedure envCode unaryCode
      (fun x : Env => MediatorParameters.scale x.1 x.2.1 x.2.2.1 +
        MediatorParameters.scale x.1 x.2.1 x.2.2.1) := add.comp (scale.pair scale)
  exact (mul.comp (twice.pair wProgram)).congrFun (by intro x; simp only [Function.comp_apply, two_mul])
end ContinuumCoulomb.MediatorUnaryProgram

end OAI
