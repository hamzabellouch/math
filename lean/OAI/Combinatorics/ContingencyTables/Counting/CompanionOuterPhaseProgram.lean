import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartSchedule
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseTrialProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitializedRestartProgram

namespace OAI

/-! # One complete adaptive phase from the stored chronological history -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Request := (Prepared×Stored)×List Stored
abbrev Input := Request×List Bool
local instance : Codec CompanionObservedUpdateProgram.Configs := inferInstance
local instance : Codec CompanionObservedUpdateProgram.Base := inferInstance
local instance : Codec (CompanionObservedUpdateProgram.Configs×CompanionObservedUpdateProgram.Base) := inferInstance
local instance : Codec CompanionObservedUpdateProgram.Input := inferInstance
local instance : Codec (Prepared×Stored) := inferInstance
local instance : Codec Request := inferInstance
local instance : Codec Input := inferInstance

def history (z : Input) : List Stored := z.1.2
def historyRealizer : Realizer history := composition first second
lemma polynomial_history : PolynomialTime historyRealizer :=
  polynomial_composition polynomial_first polynomial_second

def phase (z : Input) : ℕ := (history z).length
def phaseRealizer : Realizer phase :=
  composition (f := history) (g := List.length) historyRealizer listLength
lemma polynomial_phase : PolynomialTime phaseRealizer :=
  polynomial_composition polynomial_history polynomial_listLength

def old (z : Input) : Stored :=
  if phase z=0 then z.1.1.2 else (history z).getD (phase z-1) default
def oldRealizer : Realizer old :=
  (choose (composition (pair phaseRealizer (constant 0)) natEqual)
    (composition (composition first first) second)
    (composition (pair historyRealizer (composition (pair phaseRealizer (constant 1)) subtract))
      (getDFast default))).congr (by intro z; simp only [old,Function.comp_apply,decide_eq_true_eq])
lemma polynomial_old : PolynomialTime oldRealizer := by
  unfold oldRealizer
  apply polynomial_congr
  exact polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_phase (polynomial_constant 0)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_history
      (polynomial_composition (polynomial_pair polynomial_phase (polynomial_constant 1)) polynomial_subtract))
      (polynomial_getDFast default))

def reserve (z : Input) : List Bool := z.2.map (fun _ => false)
def reserveRealizer : Realizer reserve := composition second (map (constant false))
lemma polynomial_reserve : PolynomialTime reserveRealizer :=
  polynomial_composition polynomial_second (polynomial_map (polynomial_constant false))

def contextInput (z : Input×ℕ) : CompanionPhaseContextProgram.Input :=
  (((z.1.1.1.1,phase z.1+z.2),reserve z.1))
def contextInputRealizer : Realizer contextInput :=
  pair (pair (composition (composition (composition first first) first) first)
    (composition (pair (composition (f := Prod.fst) (g := phase) first phaseRealizer) second) add))
    (composition (f := Prod.fst) (g := reserve) first reserveRealizer)
lemma polynomial_contextInput : PolynomialTime contextInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_phase)
      polynomial_second) polynomial_add)) (polynomial_composition polynomial_first polynomial_reserve)

def configAt (i : ℕ) (z : Input) : RootedLabelWeightProgram.Config :=
  CompanionPhaseContextProgram.config (contextInput (z,i))
def configAtRealizer (i : ℕ) : Realizer (configAt i) :=
  composition (f := fun z : Input => contextInput (z,i)) (g := CompanionPhaseContextProgram.config)
    (composition (f := fun z : Input => (z,i)) (g := contextInput)
      (pair identity (constant i)) contextInputRealizer) CompanionPhaseContextProgram.configRealizer
lemma polynomial_configAt (i : ℕ) : PolynomialTime (configAtRealizer i) :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant i))
    polynomial_contextInput) CompanionPhaseContextProgram.polynomial_config

def restartRequest (z : Input) : Prepared×List Stored := (z.1.1.1,history z)
def restartRequestRealizer : Realizer restartRequest :=
  pair (composition (composition first first) first) historyRealizer
lemma polynomial_restartRequest : PolynomialTime restartRequestRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_first) polynomial_history

def restartWidth (z : Input) : ℕ := CompanionRestartSchedule.width (restartRequest z)
def restartWidthRealizer : Realizer restartWidth :=
  composition (f := restartRequest) (g := CompanionRestartSchedule.width)
    restartRequestRealizer CompanionRestartSchedule.widthRealizer
lemma polynomial_restartWidth : PolynomialTime restartWidthRealizer :=
  polynomial_composition polynomial_restartRequest CompanionRestartSchedule.polynomial_width

def restartInput (z : Input) : CompanionInitializedRestartProgram.Input :=
  (restartRequest z,z.2)
def restartInputRealizer : Realizer restartInput :=
  pair restartRequestRealizer second
lemma polynomial_restartInput : PolynomialTime restartInputRealizer :=
  polynomial_pair polynomial_restartRequest polynomial_second

def startCode (z : Input) : List ℕ := CompanionInitializedRestartProgram.output (restartInput z)
def startCodeRealizer : Realizer startCode :=
  composition (f := restartInput) (g := CompanionInitializedRestartProgram.output)
    restartInputRealizer CompanionInitializedRestartProgram.outputRealizer
lemma polynomial_startCode : PolynomialTime startCodeRealizer :=
  polynomial_composition polynomial_restartInput CompanionInitializedRestartProgram.polynomial_output

def parameters (z : Input) : CountingPhaseParametersProgram.Input := z.1.1.1.2
def parametersRealizer : Realizer parameters := composition (composition (composition first first) first) second
lemma polynomial_parameters : PolynomialTime parametersRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_first) polynomial_second

def precision (z : Input) : ℕ := CountingPhaseParametersProgram.precision (parameters z)
def precisionRealizer : Realizer precision :=
  composition (f := parameters) (g := CountingPhaseParametersProgram.precision)
    parametersRealizer CountingPhaseParametersProgram.precisionRealizer
lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition polynomial_parameters CountingPhaseParametersProgram.polynomial_precision

def observations (z : Input) : ℕ := CountingPhaseParametersProgram.observations (parameters z)
def observationsRealizer : Realizer observations :=
  composition (f := parameters) (g := CountingPhaseParametersProgram.observations)
    parametersRealizer CountingPhaseParametersProgram.observationsRealizer
lemma polynomial_observations : PolynomialTime observationsRealizer :=
  polynomial_composition polynomial_parameters CountingPhaseParametersProgram.polynomial_observations

attribute [local irreducible] old startCode configAt

def walkState (z : Input) : CompanionBoundedWalkProgram.State :=
  ((((configAt 0 z,(old z).1),precision z),startCode z),startCode z)
def walkStateRealizer : Realizer walkState :=
  pair (pair (pair (pair (configAtRealizer 0) (composition (f := old) (g := Prod.fst) oldRealizer first))
    precisionRealizer) startCodeRealizer) startCodeRealizer
lemma polynomial_walkState : PolynomialTime walkStateRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair (polynomial_pair (polynomial_configAt 0)
    (polynomial_composition polynomial_old polynomial_first)) polynomial_precision) polynomial_startCode)
    polynomial_startCode

def widthInput (z : Input) : CompanionMetropolisWordProgram.Input :=
  (((walkState z).1.1,(walkState z).2),[])
def widthInputRealizer : Realizer widthInput :=
  pair (pair (composition (composition (f := walkState) (g := Prod.fst) walkStateRealizer first) first)
    (composition (f := walkState) (g := Prod.snd) walkStateRealizer second)) (constant [])
lemma polynomial_widthInput : PolynomialTime widthInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition (polynomial_composition polynomial_walkState
    polynomial_first) polynomial_first) (polynomial_composition polynomial_walkState polynomial_second))
    (polynomial_constant [])

def trajectoryWidth (z : Input) : ℕ := observations z*CompanionTransitionWidth.width (widthInput z)
def trajectoryWidthRealizer : Realizer trajectoryWidth :=
  composition (pair observationsRealizer (composition (f := widthInput) (g := CompanionTransitionWidth.width)
    widthInputRealizer CompanionTransitionWidth.widthRealizer)) multiply
lemma polynomial_trajectoryWidth : PolynomialTime trajectoryWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_observations
    (polynomial_composition polynomial_widthInput CompanionTransitionWidth.polynomial_width)) polynomial_multiply

def afterRestart (z : Input) : List Bool := z.2.drop (restartWidth z)
def afterRestartRealizer : Realizer afterRestart := composition (pair second restartWidthRealizer) dropFast
lemma polynomial_afterRestart : PolynomialTime afterRestartRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_restartWidth) polynomial_dropFast

def trajectoryInput (z : Input) : CompanionTrajectoryProgram.Input :=
  ((walkState z,observations z),(afterRestart z).take (trajectoryWidth z))
def trajectoryInputRealizer : Realizer trajectoryInput :=
  pair (pair walkStateRealizer observationsRealizer)
    (composition (pair afterRestartRealizer trajectoryWidthRealizer) takeFast)
lemma polynomial_trajectoryInput : PolynomialTime trajectoryInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_walkState polynomial_observations)
    (polynomial_composition (polynomial_pair polynomial_afterRestart polynomial_trajectoryWidth) polynomial_takeFast)

def trialInput (z : Input) : CompanionPhaseTrialProgram.Input :=
  ((((configAt 0 z,configAt 1 z),old z),trajectoryInput z),(afterRestart z).drop (trajectoryWidth z))
def trialInputRealizer : Realizer trialInput :=
  pair (pair (pair (pair (configAtRealizer 0) (configAtRealizer 1)) oldRealizer) trajectoryInputRealizer)
    (composition (pair afterRestartRealizer trajectoryWidthRealizer) dropFast)
lemma polynomial_trialInput : PolynomialTime trialInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair (polynomial_pair (polynomial_configAt 0)
    (polynomial_configAt 1)) polynomial_old) polynomial_trajectoryInput)
    (polynomial_composition (polynomial_pair polynomial_afterRestart polynomial_trajectoryWidth) polynomial_dropFast)

attribute [local irreducible] trialInput

def fallback (p : Stored×Option Stored) : Stored := p.2.getD p.1
def fallbackRealizer : Realizer fallback :=
  (optionCases identity second).congr (by intro p; unfold fallback; cases p.2 <;> rfl)
lemma polynomial_fallback : PolynomialTime fallbackRealizer := by
  unfold fallbackRealizer
  apply polynomial_congr
  exact polynomial_optionCases polynomial_identity polynomial_second

def output (z : Input) : Stored := (CompanionPhaseTrialProgram.output (trialInput z)).getD (old z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => (old z,CompanionPhaseTrialProgram.output (trialInput z)))
    (g := fallback)
    (pair oldRealizer (composition (f := trialInput) (g := CompanionPhaseTrialProgram.output)
      trialInputRealizer CompanionPhaseTrialProgram.outputRealizer)) fallbackRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_old (polynomial_composition polynomial_trialInput
    CompanionPhaseTrialProgram.polynomial_output)) polynomial_fallback

end ContingencyTables.CompanionOuterPhaseProgram

end OAI
