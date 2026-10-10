import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.EulerVectorPrograms

namespace OAI

/-! The bounded-register Euler loop is an actual polynomial-time TM2
program whenever its field sampler is one. The size invariant was proved
for arbitrary sampler outputs, so this certificate holds on all inputs. -/

namespace ContinuumCoulomb.EulerRegisters
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

variable {E : Type} {ce : E → List Bool}

noncomputable opaque parametersProgram : Procedure (configCode ce) (parametersCode ce) Prod.fst :=
  Procedure.first (parametersCode ce) (prodCode Nat.bits registersCode)
noncomputable opaque environmentProgram : Procedure (configCode ce) ce (fun c : Config E => c.1.1) :=
  (Procedure.first ce (prodCode Nat.bits (prodCode Nat.bits ratCode))).comp parametersProgram
noncomputable opaque parameterTailProgram : Procedure (configCode ce)
    (prodCode Nat.bits (prodCode Nat.bits ratCode)) (fun c : Config E => c.1.2) :=
  (Procedure.second ce _).comp parametersProgram
noncomputable opaque denominatorProgram : Procedure (configCode ce) Nat.bits (fun c : Config E => c.1.2.1) :=
  (Procedure.first Nat.bits _).comp parameterTailProgram
noncomputable opaque boxStepProgram : Procedure (configCode ce) (prodCode Nat.bits ratCode)
    (fun c : Config E => c.1.2.2) := (Procedure.second Nat.bits _).comp parameterTailProgram
noncomputable opaque boxProgram : Procedure (configCode ce) Nat.bits (fun c : Config E => c.1.2.2.1) :=
  (Procedure.first Nat.bits ratCode).comp boxStepProgram
noncomputable opaque stepProgram : Procedure (configCode ce) ratCode (fun c : Config E => c.1.2.2.2) :=
  (Procedure.second Nat.bits ratCode).comp boxStepProgram
noncomputable opaque stateProgram : Procedure (configCode ce) (prodCode Nat.bits registersCode) Prod.snd :=
  Procedure.second (parametersCode ce) (prodCode Nat.bits registersCode)
noncomputable opaque counterProgram : Procedure (configCode ce) Nat.bits (fun c : Config E => c.2.1) :=
  (Procedure.first Nat.bits registersCode).comp stateProgram
noncomputable opaque registersProgram : Procedure (configCode ce) registersCode (fun c : Config E => c.2.2) :=
  (Procedure.second Nat.bits registersCode).comp stateProgram

noncomputable opaque currentPointProgram : Procedure (configCode ce) tripleCode
    (fun c : Config E => point c.1.2.1 c.2.2) :=
  pointProgram.comp (denominatorProgram.pair registersProgram)

noncomputable opaque timeProgram : Procedure (configCode ce) ratCode
    (fun c : Config E => (c.2.1:ℚ)*c.1.2.2.2) :=
  Procedure.ratMul.comp ((Procedure.natToRat.comp counterProgram).pair stepProgram)

noncomputable opaque sampleArgumentsProgram :
    Procedure (configCode ce) (prodCode ce (prodCode ratCode tripleCode))
      (fun c : Config E => (c.1.1,((c.2.1:ℚ)*c.1.2.2.2,point c.1.2.1 c.2.2))) :=
  environmentProgram.pair (timeProgram.pair currentPointProgram)

variable {evaluate : E → ℚ → Triple → Triple}

noncomputable opaque velocityProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) tripleCode (fun c : Config E =>
      evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2)) :=
  sampleProgram.comp sampleArgumentsProgram

noncomputable opaque proposalArgumentsProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) proposalCode (fun c : Config E =>
      (c.1.2.2.2,(point c.1.2.1 c.2.2,evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2)))) :=
  stepProgram.pair (currentPointProgram.pair (velocityProgram sampleProgram))

noncomputable opaque nextPointProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) tripleCode (fun c : Config E =>
      proposal c.1.2.2.2 (point c.1.2.1 c.2.2)
        (evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2))) :=
  proposalProgram.comp (proposalArgumentsProgram sampleProgram)

noncomputable opaque nextRegistersProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) registersCode (fun c : Config E =>
      round c.1.2.1 c.1.2.2.1 (proposal c.1.2.2.2 (point c.1.2.1 c.2.2)
        (evaluate c.1.1 ((c.2.1:ℚ)*c.1.2.2.2) (point c.1.2.1 c.2.2)))) :=
  roundProgram.comp ((denominatorProgram.pair boxProgram).pair (nextPointProgram sampleProgram))

noncomputable opaque advanceProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (configCode ce) (configCode ce) (advance evaluate) :=
  parametersProgram.pair ((Procedure.successor.comp counterProgram).pair
    (nextRegistersProgram sampleProgram))

noncomputable opaque repeatProgram
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (prodCode unaryCode (configCode ce)) (configCode ce)
      (fun x => (advance evaluate)^[x.1] x.2) :=
  (advanceProgram sampleProgram).iterate (32*(Polynomial.X+1)^2)
    (iterate_code_bound ce evaluate)

def run (evaluate : E → ℚ → Triple → Triple) (x : ℕ×Config E) : Triple :=
  let c := (advance evaluate)^[x.1] x.2
  point c.1.2.1 c.2.2

noncomputable opaque program
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Procedure (prodCode unaryCode (configCode ce)) tripleCode (run evaluate) :=
  currentPointProgram.comp (repeatProgram sampleProgram)

noncomputable def certificate
    (sampleProgram : Procedure (prodCode ce (prodCode ratCode tripleCode)) tripleCode
      (fun x => evaluate x.1 x.2.1 x.2.2)) :
    Turing.TM2ComputableInPolyTime (prodCode unaryCode (configCode ce)) tripleCode (run evaluate) :=
  (program sampleProgram).toTM2

end ContinuumCoulomb.EulerRegisters

end OAI
