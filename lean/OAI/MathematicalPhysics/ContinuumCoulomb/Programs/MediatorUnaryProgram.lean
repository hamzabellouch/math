import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorUnaryThird

namespace OAI

/-! Actual final unary coefficient and vertex bounds, with the arithmetic
nodes kept separate from the fixed finite machine texts. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque thirdDeltaRaw : Procedure envCode unaryCode
    ((fun x : Env => MediatorParameters.delta x.1 x.2.1 x.2.2.1) ∘ thirdEnv) :=
  delta.comp thirdProgram
noncomputable opaque thirdDelta : Procedure envCode unaryCode (fun x : Env =>
    MediatorParameters.delta (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  thirdDeltaRaw.congrFun (by intro x; rfl)
noncomputable opaque thirdSpokesRaw : Procedure envCode unaryCode
    ((fun x : Env => 2 * MediatorParameters.scale x.1 x.2.1 x.2.2.1 * x.2.1) ∘ thirdEnv) :=
  spokeBound.comp thirdProgram
noncomputable opaque thirdSpokes : Procedure envCode unaryCode (fun x : Env =>
    2 * MediatorParameters.scale (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
      MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) :=
  thirdSpokesRaw.congrFun (by intro x; rfl)
noncomputable opaque finalBase : Procedure envCode unaryCode (fun x : Env =>
    2 + MediatorParameters.delta x.1 x.2.1 x.2.2.1) :=
  add.comp ((Procedure.constant envCode unaryCode 2).pair delta)
noncomputable opaque finalHead : Procedure envCode unaryCode (fun x : Env =>
    2 + MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1) :=
  add.comp (finalBase.pair thirdDelta)
noncomputable opaque finalWeightRaw : Procedure envCode unaryCode (fun x : Env =>
    2 + MediatorParameters.delta x.1 x.2.1 x.2.2.1 +
      MediatorParameters.delta (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 +
      2 * MediatorParameters.scale (6 * x.1) (MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) x.2.2.1 *
        MediatorParameters.thirdWeight x.1 x.2.1 x.2.2.1) :=
  add.comp (finalHead.pair thirdSpokes)
noncomputable opaque finalWeight : Procedure envCode unaryCode
    (fun x : Env => MediatorParameters.finalWeight x.1 x.2.1 x.2.2.1) :=
  finalWeightRaw.congrFun (by intro x; rfl)

noncomputable opaque finalN : Procedure envCode unaryCode (fun x : Env => x.2.2.2 + 18 * x.1) :=
  add.comp (nProgram.pair (mul.comp
    ((Procedure.constant envCode unaryCode 18).pair rProgram)))

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
