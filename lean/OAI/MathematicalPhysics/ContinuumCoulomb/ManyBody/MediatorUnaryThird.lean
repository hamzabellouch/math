import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorUnarySecond

namespace OAI

/-! Actual third-stage unary coefficient and vertex metadata. Separate
opaque arithmetic nodes prevent expansion of the finite program text. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque secondDeltaRaw : Procedure envCode unaryCode
    ((fun x : Env => MediatorParameters.delta x.1 x.2.1 x.2.2.1) ∘ secondEnv) :=
  delta.comp secondProgram
noncomputable opaque secondDelta : Procedure envCode unaryCode (fun x : Env =>
    MediatorParameters.delta (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  secondDeltaRaw.congrFun (by intro x; rfl)
noncomputable opaque secondSpokesRaw : Procedure envCode unaryCode
    ((fun x : Env => 2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1) ∘ secondEnv) :=
  spokeBound.comp secondProgram
noncomputable opaque secondSpokes : Procedure envCode unaryCode (fun x : Env =>
    2 * MediatorParameters.scale (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
      MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) :=
  secondSpokesRaw.congrFun (by intro x; rfl)
noncomputable opaque thirdBase : Procedure envCode unaryCode (fun x : Env =>
    2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
  add.comp ((Procedure.constant envCode unaryCode 2).pair retainedBound)
noncomputable opaque thirdHead : Procedure envCode unaryCode (fun x : Env =>
    2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  add.comp (thirdBase.pair secondDelta)
noncomputable opaque weightThreeRaw : Procedure envCode unaryCode (fun x : Env =>
    2 + 3 * x.1 * MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 +
      2 * MediatorParameters.scale (2 * x.1) (MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
        MediatorParameters.secondWeight x.1 x.2.1 x.2.2.1) :=
  add.comp (thirdHead.pair secondSpokes)
noncomputable opaque weightThree : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) :=
  weightThreeRaw.congrFun (by intro x; rfl)

noncomputable opaque sixR : Procedure envCode unaryCode (fun x : Env => 6 * x.1) :=
  mul.comp ((Procedure.constant envCode unaryCode 6).pair rProgram)
noncomputable opaque thirdN : Procedure envCode unaryCode (fun x : Env => x.2.2.2 + 6 * x.1) :=
  add.comp (nProgram.pair sixR)

def thirdEnv (x : Env) : Env :=
  (6 * x.1, MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1, x.2.2.1, x.2.2.2 + 6 * x.1)
noncomputable opaque thirdProgramRaw : Procedure envCode envCode (fun x : Env =>
    (6 * x.1, MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1, x.2.2.1, x.2.2.2 + 6 * x.1)) :=
  sixR.pair (weightThree.pair (gProgram.pair thirdN))
noncomputable opaque thirdProgram : Procedure envCode envCode thirdEnv :=
  thirdProgramRaw.congrFun (by intro x; rfl)

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
