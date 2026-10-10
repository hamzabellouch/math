import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartInitializer
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishProgram

namespace OAI

/-! # Initialization and all stored-multiplier restart stages

Past entries are stored in chronological order. Entry i contains the
multiplier for restart phase i+1. Initialization and restart stages take
disjoint slices of the supplied word.
-/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Input := (Prepared×List Stored)×List Bool

def reserve (z : Input) : List Bool := z.2.map (fun _ => false)
def reserveRealizer : Realizer reserve := composition second (map (constant false))
lemma polynomial_reserve : PolynomialTime reserveRealizer :=
  polynomial_composition polynomial_second (polynomial_map (polynomial_constant false))

def indices (z : Input) : List ℕ := List.range z.1.2.length
def indicesRealizer : Realizer indices :=
  composition (composition (composition first second) listLength) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

def stageAt (z : Input×ℕ) : CompanionRestartProgram.Stage :=
  (((z.1.1.1,z.2+1),reserve z.1),(z.1.1.2.getD z.2 default).1)
def stageAtRealizer : Realizer stageAt := by
  let prepared : Realizer (fun z : Input×ℕ => z.1.1.1) := composition (composition first first) first
  let phase : Realizer (fun z : Input×ℕ => z.2+1) := composition second successor
  let marker : Realizer (fun z : Input×ℕ => reserve z.1) :=
    composition (f := fun z : Input×ℕ => z.1) (g := reserve) first reserveRealizer
  let stored : Realizer (fun z : Input×ℕ => z.1.1.2.getD z.2 (default : Stored)) :=
    composition (f := fun z : Input×ℕ => (z.1.1.2,z.2))
      (g := fun p : List Stored×ℕ => p.1.getD p.2 default)
      (pair (composition (composition first first) second) second) (getDFast default)
  exact pair (pair (pair prepared phase) marker) (composition (f := fun z : Input×ℕ =>
    z.1.1.2.getD z.2 (default : Stored)) (g := Prod.fst) stored first)
lemma polynomial_stageAt : PolynomialTime stageAtRealizer := by
  unfold stageAtRealizer
  apply polynomial_pair
  · exact polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition polynomial_second polynomial_successor))
      (polynomial_composition polynomial_first polynomial_reserve)
  · exact polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_second) (polynomial_getDFast default)) polynomial_first

def stages (z : Input) : List CompanionRestartProgram.Stage :=
  (indices z).map (fun i => stageAt (z,i))
def stagesRealizer : Realizer stages := composition (pair identity indicesRealizer) (mapWith stageAtRealizer)
lemma polynomial_stages : PolynomialTime stagesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_stageAt)

def initialWidth (z : Input) : ℕ := CompanionRestartInitializer.width z.1.1
def initialWidthRealizer : Realizer initialWidth :=
  composition (f := fun z : Input => z.1.1) (g := CompanionRestartInitializer.width)
    (composition first first) CompanionRestartInitializer.widthRealizer
lemma polynomial_initialWidth : PolynomialTime initialWidthRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    CompanionRestartInitializer.polynomial_width

def initialInput (z : Input) : CompanionRestartInitializer.Input :=
  (z.1.1,z.2.take (initialWidth z))
def initialInputRealizer : Realizer initialInput :=
  pair (composition first first)
    (composition (f := fun z : Input => (z.2,initialWidth z))
      (g := fun p : List Bool×ℕ => p.1.take p.2) (pair second initialWidthRealizer) takeFast)
lemma polynomial_initialInput : PolynomialTime initialInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_initialWidth) polynomial_takeFast)

def initialCode (z : Input) : List ℕ := CompanionRestartInitializer.output (initialInput z)
def initialCodeRealizer : Realizer initialCode :=
  composition (f := initialInput) (g := CompanionRestartInitializer.output)
    initialInputRealizer CompanionRestartInitializer.outputRealizer
lemma polynomial_initialCode : PolynomialTime initialCodeRealizer :=
  polynomial_composition polynomial_initialInput CompanionRestartInitializer.polynomial_output

attribute [local irreducible] stages initialCode initialWidth

def prepare (z : Input) : CompanionRestartProgram.Input :=
  ((stages z,initialCode z),z.2.drop (initialWidth z))
def prepareRealizer : Realizer prepare :=
  pair (pair stagesRealizer initialCodeRealizer)
    (composition (f := fun z : Input => (z.2,initialWidth z))
      (g := fun p : List Bool×ℕ => p.1.drop p.2) (pair second initialWidthRealizer) dropFast)
lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_stages polynomial_initialCode)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_initialWidth) polynomial_dropFast)

def output (z : Input) : List ℕ := CompanionRestartProgram.output (prepare z)
def outputRealizer : Realizer output :=
  composition (f := prepare) (g := CompanionRestartProgram.output)
    prepareRealizer CompanionRestartProgram.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CompanionRestartProgram.polynomial_output

end ContingencyTables.CompanionInitializedRestartProgram

end OAI
