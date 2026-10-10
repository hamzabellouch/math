import Mathlib
import OAI.Computability.MinUncut.Machines.MachineTableIteration
import OAI.Computability.MinUncut.Graphs.GeneratedGraph
import OAI.Computability.MinUncut.Estimates.SelectedSyntax

namespace OAI

section
noncomputable section
namespace MinUncut.Uniform
open MinUncut.Preprocess MinUncut.Inner MinUncut.Outer MinUncut.SourceBridge
open MinUncut.Costed MinUncut.Costed.SourceWords
open MinUncutGames MinUncutGames.Foundations MinUncutGames.Foundations.Complexity
open MinUncutGames.Foundations.Hastad MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Reduction

def frontend (F : BinaryFormula.Formula) : SourceGeneratorContract.NonemptyFormula :=
  MinUncutGames.Outer.HastadSource.gapInput Parameters.baseTable (BinaryOccurrenceRename.renamed F)
def frontendMachine : Turing.TM2ComputableInPolyTime BinaryEncoding.formulaBits
    SourceGeneratorContract.inputEncoding frontend :=
  MachineSequential.composeBits (f := BinaryOccurrenceRename.renamed)
    (g := MinUncutGames.Outer.HastadSource.gapInput Parameters.baseTable) BinaryRenameMachine.computableInPolyTime
    (MinUncutGames.Outer.HastadSource.gapMachine Parameters.baseTable)
lemma frontend_finite : MachineFiniteAlphabet.FiniteAlphabet frontendMachine.tm :=
  MachineFiniteAlphabet.composeBits _ _ BinaryRenameMachine.computation_finiteAlphabet
    (TableIterationFiniteAlphabet.gapMap Parameters.baseTable
      (MinUncutGames.Outer.HastadSource.roundMachine Parameters.baseTable)
      (MinUncutGames.Outer.HastadSource.roundMachine_finite Parameters.baseTable))

def program (K : ℕ) := completeGraphProgram (selectedParameters K) (chosenEnumeration K)
  (chosenRepetition K) (chosenNoise K)
lemma program_computable : Computable (fun K=>(program K).code) := c_selectedGraphCode

def source (K : ℕ) (F : BinaryFormula.Formula) : SourceEncoding.Input :=
  (selectedParameters K).sourceReduction.reduce F
lemma source_eq (K : ℕ) (F : BinaryFormula.Formula) :
    source K F=sourceInput (frontend F).val (chosenRepetition K) (chosenNoise K)
      (SourceNoiseParameter.noiseDenominator_pos (chosenError K)) := rfl

def output (K : ℕ) (F : BinaryFormula.Formula) : MinUncut.Output :=
  generatedGraph (selectedParameters K) (source K F) (chosenEnumeration K)
lemma output_yes (K : ℕ) (F : BinaryFormula.Formula) (hF : F.Satisfiable) :
    (output K F).opt≤(output K F).threshold := by
  obtain ⟨s,hs⟩:=binaryReduction_complete (selectedParameters K).sourceReduction F hF
    (selectedParameters K).o.t (selectedParameters K).o.b4 (selectedParameters K).sourceError_budget
  exact generatedGraph_yes (selectedParameters K) (source K F) (chosenEnumeration K) s hs
lemma output_no (K : ℕ) (hK : 2≤K) (F : BinaryFormula.Formula) (hF : ¬F.Satisfiable) :
    K*(output K F).threshold<(output K F).opt := by
  apply generatedGraph_no (selectedParameters K) (source K F) (chosenEnumeration K) hK
    (show 8*K≤parameterJ K by unfold parameterJ; omega)
  exact binaryReduction_sound (selectedParameters K).sourceError_small
    (selectedParameters K).sourceReduction F hF

lemma output_words (K : ℕ) (F : BinaryFormula.Formula) :
    ∃table junk,completeGraphWords (selectedParameters K) (chosenEnumeration K)
      (chosenRepetition K) (chosenNoise K) (formulaWords (frontend F).val)=
      (output K F).vertices::((table : List Bool).map Bool.toNat++2::(output K F).threshold::junk) ∧
      (output K F).bits=BinaryEncoding.nameBits (output K F).vertices++table++
        BinaryEncoding.nameBits (output K F).threshold := by
  obtain ⟨junk,hj⟩:=completeGraphWords_spec (selectedParameters K) (chosenEnumeration K)
    (frontend F).val (chosenRepetition K) (chosenNoise K)
    (SourceNoiseParameter.noiseDenominator_pos (chosenError K)) (frontend F).property
  rw [←source_eq] at hj
  refine ⟨_,junk,hj,?_⟩
  exact GraphRegisters.listOutput_bits _ _ _
end MinUncut.Uniform

end
end

end OAI
