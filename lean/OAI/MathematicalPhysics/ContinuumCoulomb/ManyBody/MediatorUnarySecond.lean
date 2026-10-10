import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorUnaryScale

namespace OAI

/-! Actual second-stage unary coefficient and vertex metadata. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque weightTwo : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) := by
  let head : Procedure envCode unaryCode
      (fun x : Env => 2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
    add.comp ((Procedure.constant envCode unaryCode 2).pair retainedBound)
  let raw : Procedure envCode unaryCode
      (fun x : Env => 2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
        2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1) :=
    add.comp (head.pair spokeBound)
  exact raw.congrFun (by intro x; rfl)

noncomputable opaque twiceR : Procedure envCode unaryCode (fun x : Env => 2 * x.1) :=
  (add.comp (rProgram.pair rProgram)).congrFun (by intro x; simp only [Function.comp_apply]; omega)
noncomputable opaque nextN : Procedure envCode unaryCode (fun x : Env => x.2.2.2 + 2 * x.1) :=
  add.comp (nProgram.pair twiceR)

def secondEnv (x : Env) : Env :=
  (2 * x.1, MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1, x.2.2.1, x.2.2.2 + 2 * x.1)
noncomputable opaque secondProgram : Procedure envCode envCode secondEnv := by
  let raw : Procedure envCode envCode (fun x : Env =>
      (2 * x.1, MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1,
        x.2.2.1, x.2.2.2 + 2 * x.1)) :=
    twiceR.pair (weightTwo.pair (gProgram.pair nextN))
  exact raw.congrFun (by intro x; rfl)

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
