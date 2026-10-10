import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorListProgram

namespace OAI

/-! Actual unary arithmetic, projections, and a small repeated-doubling
program for the fixed mediator scale constant. -/

namespace ContinuumCoulomb.MediatorUnaryProgram
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

theorem delta_as_mul (r W G : ℕ) :
    MediatorParameters.scale r W G * MediatorParameters.scale r W G = MediatorParameters.delta r W G := by
  unfold MediatorParameters.delta
  rw [pow_two]

noncomputable opaque add : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 + x.2) := Procedure.unaryAdd
noncomputable opaque mul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x => x.1 * x.2) := Procedure.unaryMul

noncomputable opaque rProgram : Procedure envCode unaryCode (fun x : Env => x.1) := Procedure.first _ _
noncomputable opaque restProgram : Procedure envCode (prodCode unaryCode (prodCode unaryCode unaryCode))
    (fun x : Env => x.2) := Procedure.second _ _
noncomputable opaque wProgram : Procedure envCode unaryCode (fun x : Env => x.2.1) :=
  (Procedure.first _ _).comp restProgram
noncomputable opaque gProgram : Procedure envCode unaryCode (fun x : Env => x.2.2.1) :=
  ((Procedure.first _ _).comp (Procedure.second _ _)).comp restProgram
noncomputable opaque nProgram : Procedure envCode unaryCode (fun x : Env => x.2.2.2) :=
  ((Procedure.second _ _).comp (Procedure.second _ _)).comp restProgram

noncomputable opaque cube : Procedure unaryCode unaryCode (fun n => n ^ 3) :=
  (mul.comp ((mul.comp
    ((Procedure.identity unaryCode).pair (Procedure.identity unaryCode))).pair
      (Procedure.identity unaryCode))).congrFun (by intro n; simp [pow_succ])

noncomputable opaque rCube : Procedure envCode unaryCode (fun x : Env => (x.1 + 1) ^ 3) :=
  cube.comp (Procedure.unarySuccessor.comp rProgram)
noncomputable opaque wCube : Procedure envCode unaryCode (fun x : Env => x.2.1 ^ 3) := cube.comp wProgram
noncomputable opaque cubicProduct : Procedure envCode unaryCode
    (fun x : Env => (x.1 + 1) ^ 3 * x.2.1 ^ 3) := mul.comp (rCube.pair wCube)
noncomputable opaque double : Procedure unaryCode unaryCode (fun n => 2 * n) :=
  (add.comp ((Procedure.identity unaryCode).pair
    (Procedure.identity unaryCode))).congrFun (by intro n; simp only [Function.comp_apply, id_eq]; omega)

/-- Emit the fixed scale constant by twenty doublings. This keeps the
finite machine description small instead of hardcoding a million pushes. -/
noncomputable opaque powerTwoStep (k : ℕ)
    (p : Procedure envCode unaryCode (fun _ => 2 ^ k)) :
    Procedure envCode unaryCode (fun _ => 2 ^ (k + 1)) :=
  (double.comp p).congrFun (by
    intro x
    simp only [Function.comp_apply, pow_succ]
    omega)

noncomputable def powerTwoConstant : (k : ℕ) → Procedure envCode unaryCode (fun _ => 2 ^ k)
  | 0 => Procedure.constant envCode unaryCode 1
  | k + 1 => powerTwoStep k (powerTwoConstant k)

noncomputable opaque scaleConstant : Procedure envCode unaryCode (fun _ => 1048576) :=
  (powerTwoConstant 20).congrFun (by intro x; norm_num)

end ContinuumCoulomb.MediatorUnaryProgram

end OAI
