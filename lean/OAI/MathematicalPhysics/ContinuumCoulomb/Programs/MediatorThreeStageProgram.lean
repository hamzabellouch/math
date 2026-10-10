import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorUnaryProgram

namespace OAI

/-! The actual finite-stack program for all three simultaneous mediator
stages. It retains the first central bonds, subdivides the first spokes,
then subdivides all resulting six-bond paths. -/

namespace ContinuumCoulomb.MediatorThreeStageProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque environment : Procedure inputCode envCode Prod.fst := Procedure.first _ _

noncomputable opaque secondInput : Procedure inputCode inputCode
    (fun x => (MediatorUnaryProgram.secondEnv x.1, MediatorListProgram.spokes x)) :=
  (MediatorUnaryProgram.secondProgram.comp environment).pair spokesProgram

noncomputable opaque secondPaths : Procedure inputCode (listCode bondCode)
    (fun x => central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
      spokes (MediatorUnaryProgram.secondEnv x.1, spokes x)) :=
  stageProgram.comp secondInput

noncomputable opaque thirdInput : Procedure inputCode inputCode
    (fun x => (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x))) :=
  (MediatorUnaryProgram.thirdProgram.comp environment).pair secondPaths

def finalBonds (x : Input) : List Bond :=
  central x ++
    central (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x)) ++
    spokes (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x))

noncomputable opaque bondsProgram : Procedure inputCode (listCode bondCode) finalBonds :=
  ((Procedure.listAppend bondCode zeroBond).comp
    (centralProgram.pair (stageProgram.comp thirdInput))).congrFun
      (by intro x; exact (List.append_assoc _ _ _).symm)

noncomputable opaque verticesProgram : Procedure inputCode unaryCode
    (fun x => x.1.2.2.2 + 18 * x.1.1) :=
  MediatorUnaryProgram.finalN.comp environment

noncomputable opaque boundProgram : Procedure inputCode unaryCode
    (fun x => MediatorParameters.finalWeight x.1.1 x.1.2.1 x.1.2.2.1) :=
  MediatorUnaryProgram.finalWeight.comp environment

def outputCode (x : Input) : List Bool :=
  prodCode unaryCode (prodCode unaryCode (listCode bondCode))
    (x.1.2.2.2 + 18 * x.1.1,
      MediatorParameters.finalWeight x.1.1 x.1.2.1 x.1.2.2.1, finalBonds x)

noncomputable opaque outputProgram : Procedure inputCode outputCode id :=
  (verticesProgram.pair (boundProgram.pair bondsProgram)).result (by intro x; rfl)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode outputCode id :=
  outputProgram.toTM2

theorem finalBonds_length (x : Input) : (finalBonds x).length = 19 * x.2.length := by
  simp only [finalBonds, List.length_append, central, spokes, List.length_map, List.length_range]
  omega

end ContinuumCoulomb.MediatorThreeStageProgram

end OAI
