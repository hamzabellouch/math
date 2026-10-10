import Mathlib
import OAI.Computability.MaxCut.PCP.TableIteration
import OAI.Computability.MaxCut.PCP.RoundComputation
import OAI.Computability.MaxCut.Games.Probability
import OAI.Computability.MaxCut.Machines.MachineLazyTableRuntime
import OAI.Computability.MaxCut.Machines.MachineTableIteration

namespace OAI

namespace MaxCutGames.Outer.HastadSource

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

def success (input : SourceEncoding.Input) (bits : Fin input.«variables» → Bool) : ℚ :=
  (input.equations.countP (fun e => CloneGap.satisfied e bits) : ℚ) /
    input.equations.length

def asSource (input : SourceEncoding.Input) : Source :=
  Source.ofList input.equations input.nonempty

theorem failure_add_success (input : SourceEncoding.Input)
    (bits : Fin input.«variables» → Bool) :
    (asSource input).failure bits + success input bits = 1 := by
  have h := SourceProbability.failure_add_satisfaction (asSource input) bits
  rw [show (asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

def gapInput (H : RoundTables.BaseTable) (F : Formula) :
    Hastad.SourceGeneratorContract.NonemptyFormula :=
  ⟨TableIteration.gapMap H F, TableIteration.gapMap_nonempty H F⟩

def sourceMap (ξ : ℚ) (hξ : 0 < ξ) :=
  Hastad.SourceGeneratorContract.errorMap PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  sourceMap ξ hξ (gapInput H F)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits, 1 - ξ ≤ success (output H ξ hξ F) bits := by
  exact Hastad.SourceGap.forError_complete PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableIteration.gapMap_completeness H F hF)

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (F : Formula) (hF : ¬ F.Satisfiable)
    (bits : Fin (output H ξ hξ F).«variables» → Bool) :
    success (output H ξ hξ F) bits ≤ (1 + ξ) / 2 := by
  exact Hastad.SourceGap.forError_sound PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableGapReduction.gapMap_clauseGap H certificate F hF) bits

noncomputable def roundMachine (H : RoundTables.BaseTable) :=
  RoundComputation.tablePolynomialTime H (PreprocessingRuntime.tablePolynomialTime H)

theorem roundMachine_finite (H : RoundTables.BaseTable) :
    FiniteAlphabet (roundMachine H).tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet H
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)

noncomputable def gapMachine (H : RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime formulaBits Hastad.SourceGeneratorContract.inputEncoding
      (gapInput H) where
  toTM2ComputableAux :=
    (MachineTableIteration.gapMapCertificate H (roundMachine H)).toTM2ComputableAux
  time := (MachineTableIteration.gapMapCertificate H (roundMachine H)).time
  outputsFun F := (MachineTableIteration.gapMapCertificate H (roundMachine H)).outputsFun F

noncomputable def sourceMachine (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime Hastad.SourceGeneratorContract.inputEncoding
      SourceEncoding.inputBits (sourceMap ξ hξ) :=
  Hastad.SourceGenerator.forErrorComputableInPolyTime PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

noncomputable def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits (output H ξ hξ) :=
  MachineSequential.composeBits (f := gapInput H) (g := sourceMap ξ hξ)
    (gapMachine H) (sourceMachine ξ hξ)

theorem finiteAlphabet (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits (gapMachine H) (sourceMachine ξ hξ)
    (TableIterationFiniteAlphabet.gapMap H (roundMachine H) (roundMachine_finite H))
    (Hastad.SourceGenerator.forError_finite_work_alphabets PCPIteration.finalClauseGap ξ
      PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ)

structure Reduction (ξ : ℚ) where
  reduce : Formula → SourceEncoding.Input
  completeness : ∀ F, F.Satisfiable → ∃ bits, 1 - ξ ≤ success (reduce F) bits
  soundness : ∀ F, ¬ F.Satisfiable → ∀ bits, success (reduce F) bits ≤ (1 + ξ) / 2
  computation : Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

theorem exists_reduction (ξ : ℚ) (hξ : 0 < ξ) : Nonempty (Reduction ξ) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  exact ⟨⟨output H ξ hξ, complete H ξ hξ, sound H certificate ξ hξ,
    computation H ξ hξ, finiteAlphabet H ξ hξ⟩⟩

end MaxCutGames.Outer.HastadSource

end OAI
