import OAI.Combinatorics.ContingencyTables.Counting.CountingAdaptiveInputProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionUniformPhaseWidth
import OAI.Combinatorics.ContingencyTables.Counting.CompanionHistorySize

namespace OAI

/-! # One executed positive-label counting run

The supplied word is partitioned into equally padded phase words. The phase
count only truncates a supplied list, so malformed scalar inputs do
not create an unbounded loop.
-/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Request := CountingDirectProgram.Request
abbrev Input := CountingDirectProgram.Input
abbrev Prepared := CompanionPhaseContextProgram.Prepared

def prepared (req : Request) : Prepared := CountingPreparedState.output req.1
def preparedRealizer : Realizer prepared :=
  composition (f := Prod.fst) (g := CountingPreparedState.output)
    first CountingPreparedState.outputRealizer
lemma polynomial_prepared : PolynomialTime preparedRealizer :=
  polynomial_composition polynomial_first CountingPreparedState.polynomial_output

def phaseCount (req : Request) : ℕ :=
  CountingPhaseParametersProgram.scalar (.input 2) (prepared req).2
def phaseCountRealizer : Realizer phaseCount :=
  composition (f := fun req : Request => (prepared req).2)
    (g := CountingPhaseParametersProgram.scalar (.input 2))
    (composition (f := prepared) (g := Prod.snd) preparedRealizer second)
    (CountingPhaseParametersProgram.scalarRealizer (.input 2))
lemma polynomial_phaseCount : PolynomialTime phaseCountRealizer :=
  polynomial_composition (polynomial_composition polynomial_prepared polynomial_second)
    (CountingPhaseParametersProgram.polynomial_scalar (.input 2))

def phaseWidth (req : Request) : ℕ := CompanionUniformPhaseWidth.width (prepared req)
def phaseWidthRealizer : Realizer phaseWidth :=
  composition (f := prepared) (g := CompanionUniformPhaseWidth.width)
    preparedRealizer CompanionUniformPhaseWidth.widthRealizer
lemma polynomial_phaseWidth : PolynomialTime phaseWidthRealizer :=
  polynomial_composition polynomial_prepared CompanionUniformPhaseWidth.polynomial_width

def bitCount (req : Request) : ℕ := phaseCount req*phaseWidth req
def bitCountRealizer : Realizer bitCount :=
  composition (f := fun req : Request => (phaseCount req,phaseWidth req))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair phaseCountRealizer phaseWidthRealizer) multiply
theorem polynomial_bitCount : PolynomialTime bitCountRealizer :=
  polynomial_composition (polynomial_pair polynomial_phaseCount polynomial_phaseWidth) polynomial_multiply

def words (z : Input) : List (List Bool) :=
  (wordChunks (phaseWidth z.1,z.2)).take (phaseCount z.1)
def wordsRealizer : Realizer words :=
  composition (f := fun z : Input => (wordChunks (phaseWidth z.1,z.2),phaseCount z.1))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair (composition (f := fun z : Input => (phaseWidth z.1,z.2)) (g := wordChunks)
      (pair (composition (f := Prod.fst) (g := phaseWidth) first phaseWidthRealizer) second)
      wordChunksRealizer)
      (composition (f := Prod.fst) (g := phaseCount) first phaseCountRealizer)) takeFast
lemma polynomial_words : PolynomialTime wordsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_phaseWidth) polynomial_second)
      polynomial_wordChunks)
    (polynomial_composition polynomial_first polynomial_phaseCount)) polynomial_takeFast

def start (z : Input) : CompanionOuterHistoryProgram.Fixed :=
  (CountingAdaptiveInputProgram.runInput z).1
def startRealizer : Realizer start :=
  composition (f := CountingAdaptiveInputProgram.runInput) (g := Prod.fst)
    CountingAdaptiveInputProgram.runInputRealizer first
lemma polynomial_start : PolynomialTime startRealizer :=
  polynomial_composition CountingAdaptiveInputProgram.polynomial_runInput polynomial_first

def historyInput (z : Input) : CompanionOuterHistoryProgram.Input := (start z,words z)
def historyInputRealizer : Realizer historyInput := pair startRealizer wordsRealizer
lemma polynomial_historyInput : PolynomialTime historyInputRealizer :=
  polynomial_pair polynomial_start polynomial_words

attribute [local irreducible] historyInput

def finalStored (z : Input) : CompanionOuterHistoryProgram.Stored :=
  CompanionOuterHistoryProgram.output (historyInput z)
def finalStoredRealizer : Realizer finalStored :=
  composition (f := historyInput) (g := CompanionOuterHistoryProgram.output)
    historyInputRealizer CompanionOuterHistoryProgram.outputRealizer
lemma polynomial_finalStored : PolynomialTime finalStoredRealizer :=
  polynomial_composition polynomial_historyInput CompanionOuterHistoryProgram.polynomial_output

def output (z : Input) : TreeFraction.Fraction := (finalStored z).2
def outputRealizer : Realizer output :=
  composition (f := finalStored) (g := Prod.snd) finalStoredRealizer second
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_finalStored polynomial_second

theorem phaseWidth_pos (req : Request) : 0 < phaseWidth req :=
  CompanionUniformPhaseWidth.width_pos _

theorem words_ofFn (req : Request) (bits : Fin (bitCount req)→Bool) :
    words (req,List.ofFn bits)=List.ofFn (fun i : Fin (phaseCount req) =>
      List.ofFn (fun j : Fin (phaseWidth req) => bits (finProdFinEquiv (i,j)))) := by
  change (wordChunks (phaseWidth req,List.ofFn bits)).take (phaseCount req)=_
  have hc := wordChunks_ofFn (n := phaseCount req) (k := phaseWidth req) (phaseWidth_pos req) bits
  apply (congrArg (fun xs : List (List Bool) => xs.take (phaseCount req)) hc).trans
  exact List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl)

end ContingencyTables.CountingPositiveProgram

end OAI
