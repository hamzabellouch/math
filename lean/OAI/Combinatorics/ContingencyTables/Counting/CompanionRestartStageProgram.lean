import OAI.Combinatorics.ContingencyTables.Counting.CompanionRepeatedReturnProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseContextProgram

namespace OAI

/-! # One executed warm-restart stage

The context supplies the phase, immutable oracle metadata and deterministic
precision markers. The matrix is the stored multiplier for that phase.
-/
namespace ContingencyTables.CompanionRestartStageProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

abbrev Request := (CompanionPhaseContextProgram.Input × FractionMatrix) × List ℕ
abbrev Input := Request × List Bool

def context (z : Request) : CompanionPhaseContextProgram.Input := z.1.1
def contextRealizer : Realizer context := composition first first
lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_composition polynomial_first polynomial_first

def frame (z : Request) : CompanionMetropolisProgram.Frame × ℕ :=
  ((CompanionPhaseContextProgram.config (context z),z.1.2),
    CompanionPhaseContextProgram.precision (context z))
def frameRealizer : Realizer frame :=
  pair (pair
    (composition (f := context) (g := CompanionPhaseContextProgram.config)
      contextRealizer CompanionPhaseContextProgram.configRealizer)
    (composition first second))
    (composition (f := context) (g := CompanionPhaseContextProgram.precision)
      contextRealizer CompanionPhaseContextProgram.precisionRealizer)
lemma polynomial_frame : PolynomialTime frameRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_context CompanionPhaseContextProgram.polynomial_config)
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_context CompanionPhaseContextProgram.polynomial_precision)

def cap (z : Request) : ℕ := CompanionPhaseContextProgram.scalar (.input 5) (context z)
def capRealizer : Realizer cap :=
  composition (f := context) (g := CompanionPhaseContextProgram.scalar (.input 5))
    contextRealizer (CompanionPhaseContextProgram.scalarRealizer (.input 5))
lemma polynomial_cap : PolynomialTime capRealizer :=
  polynomial_composition polynomial_context (CompanionPhaseContextProgram.polynomial_scalar _)

def repetitions (z : Request) : ℕ := CompanionPhaseContextProgram.scalar (.input 3) (context z)
def repetitionsRealizer : Realizer repetitions :=
  composition (f := context) (g := CompanionPhaseContextProgram.scalar (.input 3))
    contextRealizer (CompanionPhaseContextProgram.scalarRealizer (.input 3))
lemma polynomial_repetitions : PolynomialTime repetitionsRealizer :=
  polynomial_composition polynomial_context (CompanionPhaseContextProgram.polynomial_scalar _)

attribute [local irreducible] frame cap repetitions

def fixed (z : Request) : CompanionRepeatedReturnProgram.Fixed := ((frame z,z.2),cap z)
def fixedRealizer : Realizer fixed := pair (pair frameRealizer second) capRealizer
lemma polynomial_fixed : PolynomialTime fixedRealizer :=
  polynomial_pair (polynomial_pair polynomial_frame polynomial_second) polynomial_cap

def prepare (z : Input) : CompanionRepeatedReturnProgram.Input :=
  (((fixed z.1,z.1.2),repetitions z.1),z.2)
def prepareRealizer : Realizer prepare :=
  pair (pair (pair (composition (f := fun z : Input => z.1) (g := fixed)
    first fixedRealizer) (composition first second))
    (composition (f := fun z : Input => z.1) (g := repetitions) first repetitionsRealizer)) second
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_fixed)
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_first polynomial_repetitions)) polynomial_second

def output (z : Input) : List ℕ := CompanionRepeatedReturnProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CompanionRepeatedReturnProgram.output)
    prepareRealizer CompanionRepeatedReturnProgram.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CompanionRepeatedReturnProgram.polynomial_output

def width (z : Request) : ℕ :=
  repetitions z*CompanionRepeatedReturnProgram.blockWidth (fixed z)
def widthRealizer : Realizer width :=
  composition (f := fun z : Request =>
    (repetitions z,CompanionRepeatedReturnProgram.blockWidth (fixed z)))
    (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair repetitionsRealizer (composition (f := fixed)
      (g := CompanionRepeatedReturnProgram.blockWidth) fixedRealizer
      CompanionRepeatedReturnProgram.blockWidthRealizer)) multiply
theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair polynomial_repetitions
    (polynomial_composition polynomial_fixed CompanionRepeatedReturnProgram.polynomial_blockWidth))
    polynomial_multiply

end ContingencyTables.CompanionRestartStageProgram

end OAI
