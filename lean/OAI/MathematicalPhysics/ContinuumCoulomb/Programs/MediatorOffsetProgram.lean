import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorThreeStageProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalSumProgram

namespace OAI

/-! Exact rational threshold offsets for the fully computed mediator
construction, using actual gcd-based rational-list summation. -/

namespace ContinuumCoulomb.MediatorOffsetProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

noncomputable opaque absoluteWeight : Procedure bondCode ratCode (fun e => |e.2.2|) :=
  MediatorProgram.absoluteProgram.comp ((Procedure.second _ _).comp (Procedure.second _ _))

noncomputable opaque totalWeight : Procedure inputCode ratCode
    (fun x => (x.2.map (fun e => |e.2.2|)).sum) :=
  RationalSumProgram.sumProgram.comp
    ((Procedure.listMap zeroBond 0 absoluteWeight).comp (Procedure.second _ _))

noncomputable opaque parameters : Procedure inputCode MediatorProgram.rawCode
    (fun x => (x.1.1, x.1.2.1, x.1.2.2.1, 0)) := by
  let e := Procedure.first envCode (listCode bondCode)
  let r := MediatorUnaryProgram.rProgram.comp e
  let w := MediatorUnaryProgram.wProgram.comp e
  let g := MediatorUnaryProgram.gProgram.comp e
  exact r.pair (w.pair (g.pair (Procedure.constant inputCode ratCode 0)))

noncomputable opaque rRational : Procedure inputCode ratCode (fun x => (x.1.1 : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (MediatorUnaryProgram.rProgram.comp (Procedure.first _ _)))

noncomputable opaque penalty : Procedure inputCode ratCode
    (fun x => (MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 : ℚ)) :=
  (MediatorProgram.deltaRationalProgram.comp parameters).congrFun (by intro x; rfl)

def stageOffset (x : Input) : ℚ :=
  3 * x.1.1 * MediatorParameters.delta x.1.1 x.1.2.1 x.1.2.2.1 +
    3 * (x.2.map (fun e => |e.2.2|)).sum

noncomputable opaque stageOffsetProgram : Procedure inputCode ratCode stageOffset := by
  let three := Procedure.constant inputCode ratCode 3
  let head := Procedure.ratMul.comp ((Procedure.ratMul.comp (three.pair rRational)).pair penalty)
  let tail := Procedure.ratMul.comp (three.pair totalWeight)
  exact Procedure.ratAdd.comp (head.pair tail)

def offset (x : Input) : ℚ :=
  stageOffset x +
    stageOffset (MediatorUnaryProgram.secondEnv x.1, spokes x) +
    stageOffset (MediatorUnaryProgram.thirdEnv x.1,
      central (MediatorUnaryProgram.secondEnv x.1, spokes x) ++
        spokes (MediatorUnaryProgram.secondEnv x.1, spokes x))

noncomputable opaque offsetProgram : Procedure inputCode ratCode offset := by
  let second := stageOffsetProgram.comp MediatorThreeStageProgram.secondInput
  let third := stageOffsetProgram.comp MediatorThreeStageProgram.thirdInput
  exact Procedure.ratAdd.comp ((Procedure.ratAdd.comp (stageOffsetProgram.pair second)).pair third)

noncomputable opaque errorProgram : Procedure inputCode ratCode
    (fun x => 3 / (512 * (x.1.2.2.1 : ℚ))) := by
  let g := Procedure.natToRat.comp (Procedure.unaryToBits.comp
    (MediatorUnaryProgram.gProgram.comp (Procedure.first envCode (listCode bondCode))))
  let denom := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 512).pair g)
  exact Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode 3).pair denom)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode ratCode offset :=
  offsetProgram.toTM2

end ContinuumCoulomb.MediatorOffsetProgram

end OAI
