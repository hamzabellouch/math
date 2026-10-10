import OAI.Combinatorics.ContingencyTables.Rooted.RootedPointPenaltyProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedBinFramesProgram
import OAI.Combinatorics.ContingencyTables.Machines.BinPopulationProgram
import OAI.Combinatorics.ContingencyTables.Machines.CorrectionValueProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleWalkProgram

namespace OAI

/-! # The executed selected-root correction

The stored grid point and sampled integer point share their literal
capacity, forest, baseline and small-view arrays.  The program computes
the grid exponent, point penalty and population factor before the
bounded rational power approximation.
-/

namespace ContingencyTables.RootedCorrectionProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

abbrev State := RootedOracleWalkProgram.State
abbrev Input := (State×List ℕ)×(List Bool×List Bool)

def exponentInput (z : Input) : RootedPenaltyEvaluateProgram.Input :=
  (z.1.1.1.2.1,(z.1.1.1.2.2,z.1.1.2))
def exponentInputRealizer : Realizer exponentInput :=
  pair (composition (composition (composition (composition first first) first) second) first)
    (pair (composition (composition (composition (composition first first) first) second) second)
      (composition (composition first first) second))
lemma polynomial_exponentInput : PolynomialTime exponentInputRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_second) polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_second) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second))

def pointInput (z : Input) : RootedForestPrepareProgram.Input :=
  ((((exponentInput z).1.2.1,RootedPenaltyEvaluateProgram.width (exponentInput z).1),
    (exponentInput z).2.1),z.1.2)
def pointInputRealizer : Realizer pointInput := by
  let params : Realizer (fun z : Input => (exponentInput z).1) :=
    composition (f := exponentInput) (g := fun z => z.1) exponentInputRealizer first
  let c : Realizer (fun z : Input => (exponentInput z).1.2.1) :=
    composition (composition params second) first
  let width : Realizer (fun z : Input => RootedPenaltyEvaluateProgram.width (exponentInput z).1) :=
    composition (f := fun z : Input => (exponentInput z).1)
      (g := RootedPenaltyEvaluateProgram.width) params RootedPenaltyEvaluateProgram.widthRealizer
  exact pair (pair (pair c width)
    (composition (composition exponentInputRealizer second) first)) (composition first second)
lemma polynomial_pointInput : PolynomialTime pointInputRealizer := by
  unfold pointInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_exponentInput polynomial_first) polynomial_second)
      polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_exponentInput polynomial_first)
      RootedPenaltyEvaluateProgram.polynomial_width))
    (polynomial_composition (polynomial_composition polynomial_exponentInput polynomial_second)
      polynomial_first)) (polynomial_composition polynomial_first polynomial_second)

def binInput (z : Input) : RootedBinFramesProgram.Input :=
  ((z.1.1.1.1,(0,z.1.1.1.2.1.1.1)),((exponentInput z).2.1.1,z.1.1.2))
def binInputRealizer : Realizer binInput :=
  pair (pair (composition (composition (composition first first) first) first)
    (pair (constant 0) (composition
      (composition (composition (composition (composition (composition first first) first)
        second) first) first) first)))
    (pair (composition (composition (composition exponentInputRealizer second) first) first)
      (composition (composition first first) second))
lemma polynomial_binInput : PolynomialTime binInputRealizer :=
  polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_first)
      (polynomial_pair (polynomial_constant 0)
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition (polynomial_composition (polynomial_composition
            polynomial_first polynomial_first) polynomial_first) polynomial_second)
            polynomial_first) polynomial_first) polynomial_first)))
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_exponentInput polynomial_second) polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second))

def populationInput (z : Input) : List BinIntervalProgram.Input :=
  (RootedBinFramesProgram.frames (binInput z)).map Prod.fst
def populationInputRealizer : Realizer populationInput :=
  composition (f := fun z : Input => RootedBinFramesProgram.frames (binInput z))
    (g := fun xs : List BinVectorProgram.Frame => xs.map Prod.fst)
    (composition binInputRealizer RootedBinFramesProgram.framesRealizer) (map first)
lemma polynomial_populationInput : PolynomialTime populationInputRealizer :=
  polynomial_composition
    (polynomial_composition polynomial_binInput RootedBinFramesProgram.polynomial_frames)
    (polynomial_map polynomial_first)

def phase (z : Input) : TreeFraction.Fraction :=
  ((exponentInput z).1.2.2,RootedPenaltyEvaluateProgram.height (exponentInput z).1)
def phaseRealizer : Realizer phase :=
  pair (composition (composition (composition exponentInputRealizer first) second) second)
    (composition (f := fun z : Input => (exponentInput z).1)
      (g := RootedPenaltyEvaluateProgram.height)
      (composition exponentInputRealizer first) RootedPenaltyEvaluateProgram.heightRealizer)
lemma polynomial_phase : PolynomialTime phaseRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_exponentInput polynomial_first) polynomial_second)
    polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_exponentInput polynomial_first)
      RootedPenaltyEvaluateProgram.polynomial_height)

attribute [local irreducible] RootedPenaltyEvaluateProgram.evaluate
  RootedPointPenaltyProgram.output BinPopulationProgram.output

def exponentValue (z : Input) : ℕ :=
  RootedPenaltyEvaluateProgram.evaluate (exponentInput z)
def exponentValueRealizer : Realizer exponentValue :=
  composition (f := exponentInput) (g := RootedPenaltyEvaluateProgram.evaluate)
    exponentInputRealizer RootedPenaltyEvaluateProgram.evaluateRealizer
lemma polynomial_exponentValue : PolynomialTime exponentValueRealizer :=
  polynomial_composition polynomial_exponentInput RootedPenaltyEvaluateProgram.polynomial_evaluate

def pointValue (z : Input) : TreeFraction.Fraction :=
  RootedPointPenaltyProgram.output (pointInput z)
def pointValueRealizer : Realizer pointValue :=
  composition (f := pointInput) (g := RootedPointPenaltyProgram.output)
    pointInputRealizer RootedPointPenaltyProgram.outputRealizer
lemma polynomial_pointValue : PolynomialTime pointValueRealizer :=
  polynomial_composition polynomial_pointInput RootedPointPenaltyProgram.polynomial_output

def populationValue (z : Input) : TreeFraction.Fraction :=
  BinPopulationProgram.output (populationInput z)
def populationValueRealizer : Realizer populationValue :=
  composition (f := populationInput) (g := BinPopulationProgram.output)
    populationInputRealizer BinPopulationProgram.outputRealizer
lemma polynomial_populationValue : PolynomialTime populationValueRealizer :=
  polynomial_composition polynomial_populationInput BinPopulationProgram.polynomial_output

attribute [local irreducible] exponentValue pointValue populationValue

def frame (z : Input) : CorrectionValueProgram.Frame :=
  ((exponentValue z,phase z),pointValue z)
def frameRealizer : Realizer frame :=
  pair (pair exponentValueRealizer phaseRealizer) pointValueRealizer
lemma polynomial_frame : PolynomialTime frameRealizer :=
  polynomial_pair (polynomial_pair polynomial_exponentValue polynomial_phase) polynomial_pointValue

attribute [local irreducible] frame

def prepare (z : Input) : CorrectionValueProgram.Input := ((frame z,populationValue z),z.2)
def prepareRealizer : Realizer prepare := pair (pair frameRealizer populationValueRealizer) second
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_frame polynomial_populationValue) polynomial_second

def output (z : Input) : TreeFraction.Fraction := CorrectionValueProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CorrectionValueProgram.output)
    prepareRealizer CorrectionValueProgram.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CorrectionValueProgram.polynomial_output

end ContingencyTables.RootedCorrectionProgram

end OAI
