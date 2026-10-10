import OAI.Combinatorics.ContingencyTables.Counting.CountingPreparedState
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleConfigProgram
import OAI.Combinatorics.ContingencyTables.Machines.FractionRepetitionProgram

namespace OAI

/-! # The direct estimator for the zero-label branch

The same finite-word median evaluator handles this branch. The confidence
parameter controls the outer repetition count independently of its relative
accuracy, which is one quarter of the public accuracy.
-/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

abbrev Input := (CountingBaseProgram.Input×TreeFraction.Fraction)×List Bool

def accuracy (z : Input) : TreeFraction.Fraction := CountingBaseProgram.half (CountingBaseProgram.half z.1.1.2)
def accuracyRealizer : Realizer accuracy :=
  composition (composition (composition (composition first first) second)
    CountingBaseProgram.halfRealizer) CountingBaseProgram.halfRealizer
lemma polynomial_accuracy : PolynomialTime accuracyRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    CountingBaseProgram.polynomial_half) CountingBaseProgram.polynomial_half

def reserve (z : Input) : List Bool := z.2.map (fun _ => false)
def reserveRealizer : Realizer reserve := composition second (map (constant false))
lemma polynomial_reserve : PolynomialTime reserveRealizer :=
  polynomial_composition polynomial_second (polynomial_map (polynomial_constant false))

def oracleInput (z : Input) : RootedOracleConfigProgram.Input :=
  (((CountingPreparedState.state z.1.1,accuracy z),CountingTerminalProgram.phases z.1.1),reserve z)
def oracleInputRealizer : Realizer oracleInput :=
  pair (pair (pair (composition (f := fun z : Input => z.1.1) (g := CountingPreparedState.state)
    (composition first first) CountingPreparedState.stateRealizer) accuracyRealizer)
    (composition (f := fun z : Input => z.1.1) (g := CountingTerminalProgram.phases)
      (composition first first) CountingTerminalProgram.phasesRealizer)) reserveRealizer
lemma polynomial_oracleInput : PolynomialTime oracleInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      CountingPreparedState.polynomial_state) polynomial_accuracy)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      CountingTerminalProgram.polynomial_phases)) polynomial_reserve

def rawConfig (z : Input) : RootedLabelWeightProgram.Config := RootedOracleConfigProgram.output (oracleInput z)
def rawConfigRealizer : Realizer rawConfig :=
  composition (f := oracleInput) (g := RootedOracleConfigProgram.output)
    oracleInputRealizer RootedOracleConfigProgram.outputRealizer
lemma polynomial_rawConfig : PolynomialTime rawConfigRealizer :=
  polynomial_composition polynomial_oracleInput RootedOracleConfigProgram.polynomial_output
attribute [local irreducible] rawConfig

def context (z : Input) : RootedEstimatorLayoutProgram.Context := (rawConfig z).1.1
def contextRealizer : Realizer context := composition (composition rawConfigRealizer first) first
lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_composition (polynomial_composition polynomial_rawConfig polynomial_first) polynomial_first

def repeats (z : Input) : ℕ := FractionRepetitionProgram.count z.1.2
def repeatsRealizer : Realizer repeats :=
  composition (f := fun z : Input => z.1.2) (g := FractionRepetitionProgram.count)
    (composition first second) FractionRepetitionProgram.countRealizer
lemma polynomial_repeats : PolynomialTime repeatsRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    FractionRepetitionProgram.polynomial_count

def markers (z : Input) : List Bool×List Bool := (rawConfig z).2
def markersRealizer : Realizer markers := composition rawConfigRealizer second
lemma polynomial_markers : PolynomialTime markersRealizer :=
  polynomial_composition polynomial_rawConfig polynomial_second
attribute [local irreducible] context repeats markers

def config (z : Input) : RootedLabelWeightProgram.Config := ((context z,repeats z),markers z)
def configRealizer : Realizer config := pair (pair contextRealizer repeatsRealizer) markersRealizer
lemma polynomial_config : PolynomialTime configRealizer :=
  polynomial_pair (polynomial_pair polynomial_context polynomial_repeats) polynomial_markers
attribute [local irreducible] config

def contextWidth (z : Input) : ℕ := RootedOracleConfigProgram.contextWidth (oracleInput z)
def contextWidthRealizer : Realizer contextWidth :=
  composition (f := oracleInput) (g := RootedOracleConfigProgram.contextWidth)
    oracleInputRealizer RootedOracleConfigProgram.contextWidthRealizer
lemma polynomial_contextWidth : PolynomialTime contextWidthRealizer :=
  polynomial_composition polynomial_oracleInput RootedOracleConfigProgram.polynomial_contextWidth
attribute [local irreducible] contextWidth

def wordWidth (z : Input) : ℕ := repeats z*contextWidth z
def wordWidthRealizer : Realizer wordWidth :=
  composition (f := fun z : Input => (repeats z,contextWidth z))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair repeatsRealizer contextWidthRealizer) multiply
lemma polynomial_wordWidth : PolynomialTime wordWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_repeats polynomial_contextWidth) polynomial_multiply

def sampleBits (z : Input) : List Bool := z.2.take (wordWidth z)
def sampleBitsRealizer : Realizer sampleBits :=
  composition (f := fun z : Input => (z.2,wordWidth z))
    (g := fun p : List Bool×ℕ => p.1.take p.2) (pair second wordWidthRealizer) takeFast
lemma polynomial_sampleBits : PolynomialTime sampleBitsRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_wordWidth) polynomial_takeFast

def medianInput (z : Input) : RootedEstimatorMedianProgram.Input := ((config z).1,((config z).2,sampleBits z))
def medianInputRealizer : Realizer medianInput :=
  pair (composition configRealizer first) (pair (composition configRealizer second) sampleBitsRealizer)
lemma polynomial_medianInput : PolynomialTime medianInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_config polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_config polynomial_second) polynomial_sampleBits)

def output (z : Input) : TreeFraction.Fraction := RootedEstimatorMedianProgram.output (medianInput z)
def outputRealizer : Realizer output :=
  composition (f := medianInput) (g := RootedEstimatorMedianProgram.output)
    medianInputRealizer RootedEstimatorMedianProgram.outputRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_medianInput RootedEstimatorMedianProgram.polynomial_output


abbrev Request := CountingBaseProgram.Input×TreeFraction.Fraction

def empty (z : Request) : Input := (z,[])
def emptyRealizer : Realizer empty := pair identity (constant [])
lemma polynomial_empty : PolynomialTime emptyRealizer := polynomial_pair polynomial_identity (polynomial_constant [])

def padding (z : Request) : ℕ :=
  RootedOracleConfigProgram.rootDegree (oracleInput (empty z))+
    RootedOracleConfigProgram.depth (oracleInput (empty z))
def paddingRealizer : Realizer padding :=
  composition (pair (composition (composition emptyRealizer oracleInputRealizer)
    RootedOracleConfigProgram.rootDegreeRealizer)
    (composition (composition emptyRealizer oracleInputRealizer)
      RootedOracleConfigProgram.depthRealizer)) add
lemma polynomial_padding : PolynomialTime paddingRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_empty polynomial_oracleInput)
      RootedOracleConfigProgram.polynomial_rootDegree)
    (polynomial_composition (polynomial_composition polynomial_empty polynomial_oracleInput)
      RootedOracleConfigProgram.polynomial_depth)) polynomial_add

def budget (z : Request) : ℕ := wordWidth (empty z)+padding z
def budgetRealizer : Realizer budget :=
  composition (pair (composition emptyRealizer wordWidthRealizer) paddingRealizer) add
lemma polynomial_budget : PolynomialTime budgetRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_empty polynomial_wordWidth)
    polynomial_padding) polynomial_add

end ContingencyTables.CountingDirectProgram

end OAI
