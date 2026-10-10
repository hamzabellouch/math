import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelBlocks
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelFamily

namespace OAI

/-! A fixed six-stage literal sparse-word compiler. The final stage assigns
a private mediator to every two-local term before the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelPipeline
open ExactQuantumFactoring.BitStackProgram
open QuantumOrderedLabelData QuantumOrderedLabelFamily

abbrev Input := QuantumOrderedLabelFamily.Input
abbrev State := QuantumOrderedLabelFamily.State

def fourWeight (r j : ℚ) := QuantumPolarizedSubdivision.weight r j
def sevenWeight (r j : ℚ) := QuantumPolarizedThird.weight r j

def subdivisionStep (d : ℕ) (x : Input) : Input :=
  (x.1,value 4 (fun n xs => subdivision n d xs) fourWeight x)
def thirdStep (x : Input) : Input := (x.1,value 7 thirdBlock sevenWeight x)
def yyStep (x : Input) : Input := (x.1,value 4 yyBlock fourWeight x)
def privateStep (x : Input) : Input := (x.1,value 4 privateBlock fourWeight x)
def output (x : Input) : State :=
  (privateStep (thirdStep (yyStep (thirdStep (subdivisionStep 2 (subdivisionStep 3 x)))))).2

noncomputable opaque subdivisionStepProgram (d : ℕ) : Procedure inputCode inputCode
    (subdivisionStep d) :=
  precisionProgram.pair (valueProgram 4 _ fourWeight
    (blockProgram 4 _ fourWeight (subdivisionProgram d) QuantumOrderedWeightProgram.fourProgram))
noncomputable opaque thirdStepProgram : Procedure inputCode inputCode thirdStep :=
  precisionProgram.pair (valueProgram 7 thirdBlock sevenWeight
    (blockProgram 7 thirdBlock sevenWeight thirdBlockProgram QuantumOrderedWeightProgram.sevenProgram))
noncomputable opaque yyStepProgram : Procedure inputCode inputCode yyStep :=
  precisionProgram.pair (valueProgram 4 yyBlock fourWeight
    (blockProgram 4 yyBlock fourWeight yyBlockProgram QuantumOrderedWeightProgram.fourProgram))
noncomputable opaque privateStepProgram : Procedure inputCode inputCode privateStep :=
  precisionProgram.pair (valueProgram 4 privateBlock fourWeight
    (blockProgram 4 privateBlock fourWeight privateBlockProgram QuantumOrderedWeightProgram.fourProgram))
noncomputable opaque outputProgram : Procedure inputCode stateCode output :=
  (Procedure.second unaryCode stateCode).comp (privateStepProgram.comp
    (thirdStepProgram.comp (yyStepProgram.comp (thirdStepProgram.comp
      ((subdivisionStepProgram 2).comp (subdivisionStepProgram 3))))))

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode stateCode output :=
  outputProgram.toTM2

theorem output_length (x : Input) : (output x).2.length=12544*x.2.2.length := by
  simp only [output,privateStep,thirdStep,yyStep,subdivisionStep,value,family_length]
  omega

theorem output_qubits (x : Input) : (output x).1=x.2.1+3717*x.2.2.length := by
  simp only [output,privateStep,thirdStep,yyStep,subdivisionStep,value,family_length]
  omega

end ContinuumCoulomb.QuantumOrderedLabelPipeline

end

end OAI
