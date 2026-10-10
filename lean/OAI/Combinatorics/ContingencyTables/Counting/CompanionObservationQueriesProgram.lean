import OAI.Combinatorics.ContingencyTables.Rooted.RootedLabelWeightProgram
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram

namespace OAI

/-! # Executed current and next weight queries along a supplied trajectory -/
namespace ContingencyTables.CompanionObservationQueriesProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

abbrev Config := RootedLabelWeightProgram.Config
abbrev Fraction := TreeFraction.Fraction
abbrev Input := (Config×Config)×(List (List ℕ)×List Bool)
abbrev PairInput := (Config×Config)×(List ℕ×List Bool)

def queryWidth (c : Config) : ℕ := c.1.2*RootedEstimatorLayoutProgram.wordWidth c.1.1
def queryWidthRealizer : Realizer queryWidth :=
  composition (pair (composition first second)
    (composition (f := fun c : Config => c.1.1) (g := RootedEstimatorLayoutProgram.wordWidth)
      (composition first first) RootedEstimatorLayoutProgram.wordWidthRealizer)) multiply
lemma polynomial_queryWidth : PolynomialTime queryWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      RootedEstimatorLayoutProgram.polynomial_wordWidth)) polynomial_multiply

attribute [local irreducible] queryWidth

abbrev blockWidth (cs : Config×Config) : ℕ := queryWidth cs.1+queryWidth cs.2
def blockWidthRealizer : Realizer blockWidth :=
  composition (pair (composition (f := fun cs : Config×Config => cs.1) (g := queryWidth) first queryWidthRealizer)
    (composition (f := fun cs : Config×Config => cs.2) (g := queryWidth) second queryWidthRealizer)) add
lemma polynomial_blockWidth : PolynomialTime blockWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_queryWidth)
    (polynomial_composition polynomial_second polynomial_queryWidth)) polynomial_add


def currentInput (z : PairInput) : RootedLabelWeightProgram.Input :=
  (z.1.1,(z.2.1,z.2.2.take (queryWidth z.1.1)))
def currentInputRealizer : Realizer currentInput :=
  pair (composition first first)
    (pair (composition second first)
      (composition (pair (composition second second)
        (composition (f := fun z : PairInput => z.1.1) (g := queryWidth)
          (composition first first) queryWidthRealizer)) takeFast))
lemma polynomial_currentInput : PolynomialTime currentInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_queryWidth))
        polynomial_takeFast))

def nextInput (z : PairInput) : RootedLabelWeightProgram.Input :=
  (z.1.2,(z.2.1,(z.2.2.drop (queryWidth z.1.1)).take (queryWidth z.1.2)))
def nextInputRealizer : Realizer nextInput :=
  pair (composition first second)
    (pair (composition second first)
      (composition (pair
        (composition (pair (composition second second)
          (composition (f := fun z : PairInput => z.1.1) (g := queryWidth)
            (composition first first) queryWidthRealizer)) dropFast)
        (composition (f := fun z : PairInput => z.1.2) (g := queryWidth)
          (composition first second) queryWidthRealizer)) takeFast))
lemma polynomial_nextInput : PolynomialTime nextInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_queryWidth))
          polynomial_dropFast)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_queryWidth))
        polynomial_takeFast))

attribute [local irreducible] currentInput nextInput RootedLabelWeightProgram.output

def queryPair (z : PairInput) : Fraction×Fraction :=
  (RootedLabelWeightProgram.output (currentInput z),RootedLabelWeightProgram.output (nextInput z))
def queryPairRealizer : Realizer queryPair :=
  pair (composition (f := currentInput) (g := RootedLabelWeightProgram.output)
    currentInputRealizer RootedLabelWeightProgram.outputRealizer)
    (composition (f := nextInput) (g := RootedLabelWeightProgram.output)
      nextInputRealizer RootedLabelWeightProgram.outputRealizer)
lemma polynomial_queryPair : PolynomialTime queryPairRealizer :=
  polynomial_pair (polynomial_composition polynomial_currentInput RootedLabelWeightProgram.polynomial_output)
    (polynomial_composition polynomial_nextInput RootedLabelWeightProgram.polynomial_output)

def indices (z : Input) : List ℕ := List.range z.2.1.length
def indicesRealizer : Realizer indices :=
  composition (composition (composition second first) listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_listLength) X
  intro z
  simpa only [eval_X,Function.comp_apply] using
    (list_length_le_weight z.2.1).trans ((weight_fst z.2).trans (weight_snd z))

def indexedInput (z : Input×ℕ) : PairInput :=
  (z.1.1,(z.1.2.1.getD z.2 [],wordChunk ((blockWidth z.1.1,z.1.2.2),z.2)))
def indexedInputRealizer : Realizer indexedInput :=
  pair (composition first first)
    (pair (composition (pair (composition (composition first second) first) second) (getDFast []))
      (composition (f := fun z : Input×ℕ => ((blockWidth z.1.1,z.1.2.2),z.2)) (g := wordChunk)
        (pair (pair (composition (f := fun z : Input×ℕ => z.1.1) (g := blockWidth)
          (composition first first) blockWidthRealizer) (composition (composition first second) second)) second)
        wordChunkRealizer))
lemma polynomial_indexedInput : PolynomialTime indexedInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      polynomial_second) (polynomial_getDFast []))
      (polynomial_composition (polynomial_pair (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_blockWidth)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))
        polynomial_second) polynomial_wordChunk))

def indexedPair (z : Input×ℕ) : Fraction×Fraction := queryPair (indexedInput z)
def indexedPairRealizer : Realizer indexedPair :=
  composition (f := indexedInput) (g := queryPair) indexedInputRealizer queryPairRealizer
lemma polynomial_indexedPair : PolynomialTime indexedPairRealizer :=
  polynomial_composition polynomial_indexedInput polynomial_queryPair

def output (z : Input) : List (Fraction×Fraction) := (indices z).map (fun i => indexedPair (z,i))
def outputRealizer : Realizer output :=
  composition (pair identity indicesRealizer) (mapWith indexedPairRealizer)
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_indexedPair)

end ContingencyTables.CompanionObservationQueriesProgram

end OAI
